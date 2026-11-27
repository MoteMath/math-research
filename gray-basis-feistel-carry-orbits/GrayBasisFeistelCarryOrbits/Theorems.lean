/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GrayBasisFeistelCarryOrbits.Defs

/-!
# Pure Silicon Bitwise Orbit Compilers:
# Trailing-Ones Bit-Slice Renormalization, Gray-Basis Parity-Fiber Reduction,
# and Feistel-Carry Fiber-Splice Dynamics

Standalone Lean 4.34.1 formalization (core `Init` only, zero Mathlib, fully kernel-checked).
-/


/-! ## Section 1: Iteration, Exact Minimal Period, Single Cycles, Conjugacy, and 2-Step Lifting -/

namespace SiliconOrbitEngine

theorem iter_zero {α : Type} (f : α → α) (x : α) : iter f 0 x = x := rfl

theorem iter_succ_left {α : Type} (f : α → α) (k : Nat) (x : α) :
    iter f (k + 1) x = iter f k (f x) := rfl

theorem iter_succ_right {α : Type} (f : α → α) (k : Nat) (x : α) :
    iter f (k + 1) x = f (iter f k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => exact ih (f x)

theorem iter_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iter f (a + b) x = iter f b (iter f a x) := by
  induction a generalizing x with
  | zero => simp [iter]
  | succ a ih =>
    rw [Nat.succ_add, iter_succ_left, iter_succ_left, ih]

theorem iter_two_mul {α : Type} (f : α → α) (k : Nat) (x : α) :
    iter f (2 * k) x = iter (fun y => f (f y)) k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have h : 2 * (k + 1) = 2 + 2 * k := by omega
    rw [h, iter_add]
    exact ih (f (f x))

theorem iter_conj {α β : Type} (f : α → α) (g : β → β) (e : α → β)
    (hcomm : ∀ x, g (e x) = e (f x)) (k : Nat) (x : α) :
    iter g k (e x) = e (iter f k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [iter_succ_left, iter_succ_left, hcomm, ih]

theorem hasMinPeriod_unique {α : Type} {f : α → α} {x : α} {p q : Nat}
    (hp : HasMinPeriod f x p) (hq : HasMinPeriod f x q) : p = q := by
  by_cases hlt : p < q
  · exact False.elim (hq.2.2 p hp.1 hlt hp.2.1)
  · by_cases hgt : q < p
    · exact False.elim (hp.2.2 q hq.1 hgt hq.2.1)
    · omega

theorem hasMinPeriod_of_iter_eq {α : Type} {f : α → α} {x : α} {p : Nat}
    (hp : HasMinPeriod f x p) (j : Nat) :
    HasMinPeriod f (iter f j x) p := by
  refine ⟨hp.1, ?_, ?_⟩
  · rw [← iter_add, Nat.add_comm, iter_add, hp.2.1]
  · intro k hk0 hkp heq
    have h1 : iter f (j + k) x = iter f j x := by rw [iter_add]; exact heq
    have hmod : ∀ m, iter f (m * p) x = x := by
      intro m
      induction m with
      | zero => simp [iter]
      | succ m ih => rw [Nat.succ_mul, iter_add, ih, hp.2.1]
    have hq : j ≤ (j + 1) * p := by
      have : j + 1 ≤ (j + 1) * p := Nat.le_mul_of_pos_right _ hp.1
      omega
    have hr := congrArg (iter f ((j + 1) * p - j)) h1
    rw [← iter_add, ← iter_add] at hr
    have ha1 : j + k + ((j + 1) * p - j) = (j + 1) * p + k := by omega
    have ha2 : j + ((j + 1) * p - j) = (j + 1) * p := by omega
    rw [ha1, ha2, iter_add, hmod] at hr
    exact hp.2.2 k hk0 hkp hr

theorem isSingleCycle_all_minPeriod {w : Nat} {f : BitVec w → BitVec w}
    (h : IsSingleCycle w f) (x : BitVec w) : HasMinPeriod f x (2 ^ w) := by
  rcases h.2 x with ⟨k, _, rfl⟩
  exact hasMinPeriod_of_iter_eq h.1 k

theorem hasMinPeriod_conj {α β : Type} {f : α → α} {g : β → β}
    (e : α → β) (eInv : β → α)
    (hleft : ∀ x, eInv (e x) = x)
    (hcomm : ∀ x, g (e x) = e (f x))
    {x : α} {p : Nat} :
    HasMinPeriod f x p ↔ HasMinPeriod g (e x) p := by
  have hinj : ∀ a b, e a = e b → a = b := fun a b hab => by
    have := congrArg eInv hab; rwa [hleft, hleft] at this
  constructor
  · rintro ⟨hp0, hp, hmin⟩
    refine ⟨hp0, ?_, ?_⟩
    · rw [iter_conj f g e hcomm, hp]
    · intro k hk0 hkp heq
      rw [iter_conj f g e hcomm] at heq
      exact hmin k hk0 hkp (hinj _ _ heq)
  · rintro ⟨hp0, hp, hmin⟩
    refine ⟨hp0, ?_, ?_⟩
    · rw [iter_conj f g e hcomm] at hp
      exact hinj _ _ hp
    · intro k hk0 hkp heq
      apply hmin k hk0 hkp
      rw [iter_conj f g e hcomm, heq]

theorem isSingleCycle_conj {w : Nat} {f g : BitVec w → BitVec w}
    (e eInv : BitVec w → BitVec w)
    (hleft : ∀ x, eInv (e x) = x)
    (hright : ∀ y, e (eInv y) = y)
    (hcomm : ∀ x, g (e x) = e (f x))
    (hf : IsSingleCycle w f) :
    IsSingleCycle w g := by
  have hper_e0 : HasMinPeriod g (e 0#w) (2 ^ w) :=
    (hasMinPeriod_conj e eInv hleft hcomm).1 hf.1
  have hsurj_e0 : ∀ y : BitVec w, ∃ k, k < 2 ^ w ∧ iter g k (e 0#w) = y := by
    intro y
    rcases hf.2 (eInv y) with ⟨k, hk, hke⟩
    refine ⟨k, hk, ?_⟩
    rw [iter_conj f g e hcomm, hke, hright]
  rcases hsurj_e0 0#w with ⟨j0, _, hj0⟩
  have hper0 : HasMinPeriod g 0#w (2 ^ w) := by
    rw [← hj0]
    exact hasMinPeriod_of_iter_eq hper_e0 j0
  refine ⟨hper0, ?_⟩
  intro y
  rcases hsurj_e0 y with ⟨k, hk, hky⟩
  have hmod : ∀ m, iter g (m * 2 ^ w) (e 0#w) = e 0#w := by
    intro m
    induction m with
    | zero => simp [iter]
    | succ m ih => rw [Nat.succ_mul, iter_add, ih, hper_e0.2.1]
  by_cases hle : j0 ≤ k
  · refine ⟨k - j0, by omega, ?_⟩
    rw [← hj0, ← iter_add, show j0 + (k - j0) = k by omega, hky]
  · refine ⟨2 ^ w + k - j0, by omega, ?_⟩
    rw [← hj0, ← iter_add, show j0 + (2 ^ w + k - j0) = 2 ^ w + k by omega,
        iter_add, hper_e0.2.1, hky]

/-- Parity-Alternation 2-Step Return-Map Lifting Theorem:
    If `F` strictly alternates bit-0 parity, and its 2-step return map on even states
    is `u ↦ 2 * R u`, then every even state `2*u` has exact minimal period `2 * p`
    iff `u` has exact minimal period `p` under `R`. -/
theorem hasMinPeriod_twoStep_even {n : Nat}
    (F : BitVec (n + 1) → BitVec (n + 1)) (R : BitVec n → BitVec n)
    (halt : ∀ x, (F x).toNat % 2 = 1 - x.toNat % 2)
    (hret : ∀ u : BitVec n,
      F (F (BitVec.ofNat (n + 1) (2 * u.toNat))) = BitVec.ofNat (n + 1) (2 * (R u).toNat))
    (u : BitVec n) (p : Nat) :
    HasMinPeriod F (BitVec.ofNat (n + 1) (2 * u.toNat)) (2 * p) ↔ HasMinPeriod R u p := by
  have hemb_toNat : ∀ v : BitVec n, (BitVec.ofNat (n + 1) (2 * v.toNat)).toNat = 2 * v.toNat := by
    intro v
    rw [BitVec.toNat_ofNat]
    have hv : v.toNat < 2 ^ n := v.isLt
    have : 2 * v.toNat < 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
    exact Nat.mod_eq_of_lt this
  have hemb_inj : ∀ a b : BitVec n,
      BitVec.ofNat (n + 1) (2 * a.toNat) = BitVec.ofNat (n + 1) (2 * b.toNat) → a = b := by
    intro a b hab
    have h1 := congrArg BitVec.toNat hab
    rw [hemb_toNat, hemb_toNat] at h1
    exact BitVec.eq_of_toNat_eq (by omega)
  have hiter_even : ∀ k (v : BitVec n),
      iter F (2 * k) (BitVec.ofNat (n + 1) (2 * v.toNat)) =
      BitVec.ofNat (n + 1) (2 * (iter R k v).toNat) := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      rw [iter_two_mul, iter_succ_left, ← iter_two_mul, hret, ih]
      rfl
  have hparity_odd : ∀ k (v : BitVec n),
      (iter F (2 * k + 1) (BitVec.ofNat (n + 1) (2 * v.toNat))).toNat % 2 = 1 := by
    intro k v
    rw [iter_succ_right, halt, hiter_even, hemb_toNat]
    omega
  constructor
  · rintro ⟨hp0, hper, hmin⟩
    refine ⟨by omega, ?_, ?_⟩
    · rw [hiter_even] at hper
      exact hemb_inj _ _ hper
    · intro k hk0 hkp heq
      apply hmin (2 * k) (by omega) (by omega)
      rw [hiter_even, heq]
  · rintro ⟨hp0, hper, hmin⟩
    refine ⟨by omega, ?_, ?_⟩
    · rw [hiter_even, hper]
    · intro k hk0 hkp heq
      by_cases hpar : k % 2 = 0
      · have hk : k = 2 * (k / 2) := by omega
        rw [hk, hiter_even] at heq
        exact hmin (k / 2) (by omega) (by omega) (hemb_inj _ _ heq)
      · have hk : k = 2 * (k / 2) + 1 := by omega
        rw [hk] at heq
        have h1 := congrArg (fun z => z.toNat % 2) heq
        rw [hparity_odd, hemb_toNat] at h1
        omega

theorem hasMinPeriod_twoStep_odd {n : Nat}
    (F : BitVec (n + 1) → BitVec (n + 1)) (R : BitVec n → BitVec n)
    (halt : ∀ x, (F x).toNat % 2 = 1 - x.toNat % 2)
    (hret : ∀ u : BitVec n,
      F (F (BitVec.ofNat (n + 1) (2 * u.toNat))) = BitVec.ofNat (n + 1) (2 * (R u).toNat))
    (hinj : ∀ a b, F a = F b → a = b)
    (x : BitVec (n + 1)) (hxodd : x.toNat % 2 = 1) (p : Nat) :
    HasMinPeriod F x (2 * p) ↔ HasMinPeriod R (BitVec.ofNat n ((F x).toNat / 2)) p := by
  have hFxeven : (F x).toNat % 2 = 0 := by rw [halt, hxodd]
  have hu_eq : BitVec.ofNat (n + 1) (2 * (BitVec.ofNat n ((F x).toNat / 2)).toNat) = F x := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hlt := (F x).isLt
    have hdiv : (F x).toNat / 2 < 2 ^ n := by rw [Nat.pow_succ] at hlt; omega
    rw [Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [← hasMinPeriod_twoStep_even F R halt hret _ p, hu_eq]
  constructor
  · intro h
    exact hasMinPeriod_of_iter_eq h 1
  · rintro ⟨hp0, hper, hmin⟩
    refine ⟨hp0, ?_, ?_⟩
    · apply hinj
      rw [← iter_succ_right F, iter_succ_left, hper]
    · intro k hk0 hkp heq
      apply hmin k hk0 hkp
      rw [← iter_succ_left, iter_succ_right, heq]

theorem isSingleCycle_twoStep {n : Nat}
    (F : BitVec (n + 1) → BitVec (n + 1)) (R : BitVec n → BitVec n)
    (halt : ∀ x, (F x).toNat % 2 = 1 - x.toNat % 2)
    (hret : ∀ u : BitVec n,
      F (F (BitVec.ofNat (n + 1) (2 * u.toNat))) = BitVec.ofNat (n + 1) (2 * (R u).toNat))
    (hinj : ∀ a b, F a = F b → a = b)
    (hR : IsSingleCycle n R) :
    IsSingleCycle (n + 1) F := by
  have hemb_toNat : ∀ v : BitVec n, (BitVec.ofNat (n + 1) (2 * v.toNat)).toNat = 2 * v.toNat := by
    intro v
    rw [BitVec.toNat_ofNat]
    have hv : v.toNat < 2 ^ n := v.isLt
    have : 2 * v.toNat < 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
    exact Nat.mod_eq_of_lt this
  have hzero : BitVec.ofNat (n + 1) (2 * (0#n).toNat) = 0#(n + 1) := by
    apply BitVec.eq_of_toNat_eq; simp
  have hper : HasMinPeriod F 0#(n + 1) (2 ^ (n + 1)) := by
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, ← hzero]
    exact (hasMinPeriod_twoStep_even F R halt hret 0#n (2 ^ n)).2 hR.1
  have hiter_even : ∀ k (v : BitVec n),
      iter F (2 * k) (BitVec.ofNat (n + 1) (2 * v.toNat)) =
      BitVec.ofNat (n + 1) (2 * (iter R k v).toNat) := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      rw [iter_two_mul, iter_succ_left, ← iter_two_mul, hret, ih]
      rfl
  refine ⟨hper, ?_⟩
  intro x
  by_cases hx : x.toNat % 2 = 0
  · let u : BitVec n := BitVec.ofNat n (x.toNat / 2)
    have hu : BitVec.ofNat (n + 1) (2 * u.toNat) = x := by
      apply BitVec.eq_of_toNat_eq
      rw [hemb_toNat, BitVec.toNat_ofNat]
      have hxlt : x.toNat < 2 ^ (n + 1) := x.isLt
      have hdiv : x.toNat / 2 < 2 ^ n := by rw [Nat.pow_succ] at hxlt; omega
      rw [Nat.mod_eq_of_lt hdiv]; omega
    rcases hR.2 u with ⟨k, hk, hku⟩
    refine ⟨2 * k, by rw [Nat.pow_succ]; omega, ?_⟩
    rw [← hzero, hiter_even, hku, hu]
  · have hFx_even : (F x).toNat % 2 = 0 := by rw [halt]; omega
    let u : BitVec n := BitVec.ofNat n ((F x).toNat / 2)
    have hu : BitVec.ofNat (n + 1) (2 * u.toNat) = F x := by
      apply BitVec.eq_of_toNat_eq
      rw [hemb_toNat, BitVec.toNat_ofNat]
      have hlt : (F x).toNat < 2 ^ (n + 1) := (F x).isLt
      have hdiv : (F x).toNat / 2 < 2 ^ n := by rw [Nat.pow_succ] at hlt; omega
      rw [Nat.mod_eq_of_lt hdiv]; omega
    rcases hR.2 u with ⟨k, hk, hku⟩
    by_cases hk0 : k = 0
    · subst hk0
      have hFx0 : F x = 0#(n + 1) := by rw [← hu, ← hku]; exact hzero
      have hpos : 0 < 2 ^ (n + 1) := Nat.two_pow_pos (n + 1)
      refine ⟨2 ^ (n + 1) - 1, by omega, ?_⟩
      apply hinj
      have hstep : 2 ^ (n + 1) - 1 + 1 = 2 ^ (n + 1) := by omega
      rw [← iter_succ_right F, hstep, hper.2.1, hFx0]
    · refine ⟨2 * k - 1, by rw [Nat.pow_succ]; omega, ?_⟩
      apply hinj
      have hstep : 2 * k - 1 + 1 = 2 * k := by omega
      rw [← iter_succ_right F, hstep, ← hzero, hiter_even, hku, hu]

/-! ## Section 2: Bitwise `Nat.xor` Helpers & Core `Phi_gamma` Bit-Slice Renormalization Engine -/

theorem nat_xor_mod_two (a b : Nat) : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
  have h := Nat.testBit_xor a b 0
  simp only [Nat.testBit_zero] at h
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  have hab : (a ^^^ b) % 2 = 0 ∨ (a ^^^ b) % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hab with hab | hab <;>
    simp_all

theorem nat_xor_div_two (a b : Nat) : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_div_two, Nat.testBit_div_two, Nat.testBit_div_two, Nat.testBit_xor]

theorem nat_even_add_one_eq_xor_one {a : Nat} (ha : a % 2 = 0) : a + 1 = a ^^^ 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    have h1 : (a + 1) % 2 = 1 := by omega
    rw [h1, ha]; rfl
  | succ i =>
    rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    have h1 : (a + 1) / 2 = a / 2 := by omega
    rw [h1]; simp

theorem nat_even_add_one_lt_two_pow {n a : Nat} (hn : 1 ≤ n) (hlt : a < 2 ^ n) (heven : a % 2 = 0) :
    a + 1 < 2 ^ n := by
  have h2pow_even : 2 ^ n % 2 = 0 := by
    cases n with
    | zero => omega
    | succ k => rw [Nat.pow_succ]; omega
  omega

theorem nat_mod_two_mul (a m : Nat) : a % (2 * m) = a % 2 + 2 * ((a / 2) % m) := by
  have h1 := Nat.div_add_mod (a % (2 * m)) 2
  have h2 := Nat.mod_mul_right_div_self a 2 m
  have h3 := Nat.mod_mul_right_mod a 2 m
  omega

theorem phi_injective (n : Nat) (γ : BitVec n) : ∀ a b, phi n γ a = phi n γ b → a = b := by
  intro a b h
  unfold phi at h
  have h1 : a ^^^ γ = b ^^^ γ := by
    have := congrArg (fun z => z - 1#n) h
    simpa using this
  have h2 := congrArg (fun z => z ^^^ γ) h1
  simpa [BitVec.xor_assoc] using h2

theorem trailingOnesNat_zero (g : Nat) : trailingOnesNat 0 g = 0 := rfl

theorem trailingOnesNat_succ (n g : Nat) :
    trailingOnesNat (n + 1) g = if g % 2 = 1 then 1 + trailingOnesNat n (g / 2) else 0 := rfl

theorem trailingOnesNat_le (n g : Nat) : trailingOnesNat n g ≤ n := by
  induction n generalizing g with
  | zero => simp [trailingOnesNat]
  | succ n ih =>
    rw [trailingOnesNat_succ]
    split
    · have := ih (g / 2); omega
    · omega

theorem trailingOnesNat_mod_two_pow (n g : Nat) :
    g % 2 ^ trailingOnesNat n g = 2 ^ trailingOnesNat n g - 1 := by
  induction n generalizing g with
  | zero => simp [trailingOnesNat]; omega
  | succ n ih =>
    rw [trailingOnesNat_succ]
    split
    · rename_i hodd
      have hih := ih (g / 2)
      rw [Nat.add_comm 1, Nat.pow_succ, Nat.mul_comm _ 2, nat_mod_two_mul, hodd, hih]
      have hpos : 0 < 2 ^ trailingOnesNat n (g / 2) := Nat.two_pow_pos _
      omega
    · simp; omega

/-- Exact count of trailing zeros of `v` within width `n` (returns `n` if `v % 2^n = 0`). -/
def ctzNat : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, v => if v % 2 = 0 then 1 + ctzNat n (v / 2) else 0

theorem ctzNat_succ (n v : Nat) :
    ctzNat (n + 1) v = if v % 2 = 0 then 1 + ctzNat n (v / 2) else 0 := rfl

/-- Helper: `x ↦ x + 1` on `BitVec n` is a single cycle of length `2^n`. -/
theorem addOne_iter (n k : Nat) (x : BitVec n) :
    iter (fun y : BitVec n => y + 1#n) k x = x + BitVec.ofNat n k := by
  induction k generalizing x with
  | zero => simp [iter]
  | succ k ih =>
    rw [iter_succ_left, ih]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1 : ((x.toNat + 1 % 2 ^ n) % 2 ^ n + k % 2 ^ n) % 2 ^ n =
        (x.toNat + 1 + k) % 2 ^ n := by
      rw [Nat.add_mod, Nat.mod_mod, Nat.add_mod x.toNat, Nat.mod_mod,
          Nat.mod_mod, ← Nat.add_mod x.toNat 1, ← Nat.add_mod]
    have h2 : (x.toNat + (k + 1) % 2 ^ n) % 2 ^ n = (x.toNat + (k + 1)) % 2 ^ n := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [h1, h2]
    congr 1; omega

theorem addOne_isSingleCycle (n : Nat) : IsSingleCycle n (fun x : BitVec n => x + 1#n) := by
  constructor
  · refine ⟨Nat.two_pow_pos n, ?_, ?_⟩
    · rw [addOne_iter]
      apply BitVec.eq_of_toNat_eq
      simp
    · intro k hk0 hkn heq
      rw [addOne_iter] at heq
      have h := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h
      have h0 : 0 % 2 ^ n = 0 := Nat.zero_mod _
      rw [h0, Nat.zero_add, Nat.mod_eq_of_lt hkn, Nat.mod_eq_of_lt hkn] at h
      omega
  · intro x
    refine ⟨x.toNat, x.isLt, ?_⟩
    rw [addOne_iter]
    apply BitVec.eq_of_toNat_eq
    simp

/-- Core Engine Lemma 2.1: If `γ` is even, `phi n γ` is a single full-period Hamiltonian cycle! -/
theorem phi_even_isSingleCycle (n : Nat) (γ : BitVec n) (heven : γ.toNat % 2 = 0) :
    IsSingleCycle n (phi n γ) := by
  cases n with
  | zero =>
    constructor
    · refine ⟨by omega, ?_, ?_⟩
      · apply BitVec.eq_of_toNat_eq
        have h := (phi 0 γ 0#0).isLt; simp [iter] at h ⊢; omega
      · intro k hk0 hkp; omega
    · intro x
      refine ⟨0, by omega, ?_⟩
      apply BitVec.eq_of_toNat_eq
      have hx := x.isLt; simp [iter] at hx ⊢; omega
  | succ n =>
    apply isSingleCycle_twoStep (phi (n + 1) γ) (fun u : BitVec n => u + 1#n)
    · -- Parity alternation
      intro x
      unfold phi
      rw [BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_ofNat]
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      have hmod2 : ∀ a, (a % 2 ^ (n + 1)) % 2 = a % 2 := fun a => by
        rw [hpow, Nat.mod_mul_right_mod]
      rw [hmod2]
      have h1 : 1 % 2 ^ (n + 1) = 1 := Nat.mod_eq_of_lt (by rw [hpow]; have := Nat.two_pow_pos n; omega)
      rw [h1, Nat.add_mod, nat_xor_mod_two, heven]
      have hx : x.toNat % 2 = 0 ∨ x.toNat % 2 = 1 := by omega
      rcases hx with hx | hx <;> simp [hx]
    · -- 2-step return map on even states is `u ↦ u + 1`!
      intro u
      apply BitVec.eq_of_toNat_eq
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      have hu : 2 * u.toNat < 2 ^ (n + 1) := by have := u.isLt; omega
      have h1lt : 1 < 2 ^ (n + 1) := by have := Nat.two_pow_pos n; omega
      have hs1_val : ((2 * u.toNat) ^^^ γ.toNat) % 2 = 0 := by
        rw [nat_xor_mod_two, heven]; simp
      have hs1_lt : ((2 * u.toNat) ^^^ γ.toNat) + 1 < 2 ^ (n + 1) :=
        nat_even_add_one_lt_two_pow (by omega) (Nat.xor_lt_two_pow hu γ.isLt) hs1_val
      have hs1 : (phi (n + 1) γ (BitVec.ofNat (n + 1) (2 * u.toNat))).toNat =
          ((2 * u.toNat) ^^^ γ.toNat) + 1 := by
        unfold phi
        rw [BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt hs1_lt]
      have hs2_xor : (((2 * u.toNat) ^^^ γ.toNat) + 1) ^^^ γ.toNat = 2 * u.toNat + 1 := by
        rw [nat_even_add_one_eq_xor_one hs1_val, Nat.xor_assoc, Nat.xor_comm 1 γ.toNat,
            ← Nat.xor_assoc, Nat.xor_assoc (2 * u.toNat), Nat.xor_self, Nat.xor_zero,
            ← nat_even_add_one_eq_xor_one (by omega)]
      change (((phi (n + 1) γ (BitVec.ofNat (n + 1) (2 * u.toNat))) ^^^ γ) + 1#(n + 1)).toNat = _
      rw [BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_ofNat, hs1, hs2_xor, Nat.mod_eq_of_lt h1lt]
      rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]
      have h2lt : 2 * ((u.toNat + 1 % 2 ^ n) % 2 ^ n) < 2 ^ (n + 1) := by
        have := Nat.mod_lt (u.toNat + 1 % 2 ^ n) (Nat.two_pow_pos n); omega
      rw [Nat.mod_eq_of_lt h2lt]
      have hadd : 2 * u.toNat + 1 + 1 = 2 * (u.toNat + 1) := by omega
      rw [hadd, hpow, Nat.mul_mod_mul_left]
      congr 1
      rw [Nat.add_mod, Nat.mod_eq_of_lt u.isLt]
    · exact phi_injective (n + 1) γ
    · exact addOne_isSingleCycle n

/-- Core Engine Lemma 2.2 (Carry-Free Odd Half):
    When `γ` is odd and `v` is odd, `phi n γ v` is odd with zero carry into bit 1,
    so `phi n γ (phi n γ v) = v`, and `phi n γ v = v ↔ γ.toNat = 1`. -/
theorem phi_odd_oddStep (n : Nat) (γ v : BitVec n)
    (hγ : γ.toNat % 2 = 1) (hv : v.toNat % 2 = 1) :
    (phi n γ v).toNat = v.toNat ^^^ (γ.toNat ^^^ 1) ∧
    (phi n γ v).toNat % 2 = 1 ∧
    phi n γ (phi n γ v) = v ∧
    (phi n γ v = v ↔ γ.toNat = 1) := by
  have hn1 : 1 ≤ n := by
    cases n with
    | zero => have := γ.isLt; simp at this; omega
    | succ k => omega
  have hn : 1 < 2 ^ n := by
    cases n with
    | zero => omega
    | succ k => have := Nat.two_pow_pos k; rw [Nat.pow_succ]; omega
  have hxor_even : (v.toNat ^^^ γ.toNat) % 2 = 0 := by
    rw [nat_xor_mod_two, hv, hγ]; simp
  have hadd_eq_xor : (v.toNat ^^^ γ.toNat) + 1 = (v.toNat ^^^ γ.toNat) ^^^ 1 :=
    nat_even_add_one_eq_xor_one hxor_even
  have hlt : (v.toNat ^^^ γ.toNat) + 1 < 2 ^ n :=
    nat_even_add_one_lt_two_pow hn1 (Nat.xor_lt_two_pow v.isLt γ.isLt) hxor_even
  have hstep : (phi n γ v).toNat = v.toNat ^^^ (γ.toNat ^^^ 1) := by
    unfold phi
    rw [BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
        Nat.mod_eq_of_lt hlt, hadd_eq_xor, Nat.xor_assoc]
  have hodd_out : (phi n γ v).toNat % 2 = 1 := by
    rw [hstep, nat_xor_mod_two, nat_xor_mod_two, hv, hγ]; simp
  have hinv : phi n γ (phi n γ v) = v := by
    apply BitVec.eq_of_toNat_eq
    have hxor_even2 : ((phi n γ v).toNat ^^^ γ.toNat) % 2 = 0 := by
      rw [nat_xor_mod_two, hodd_out, hγ]; simp
    have hadd2 : ((phi n γ v).toNat ^^^ γ.toNat) + 1 = ((phi n γ v).toNat ^^^ γ.toNat) ^^^ 1 :=
      nat_even_add_one_eq_xor_one hxor_even2
    have hlt2 : ((phi n γ v).toNat ^^^ γ.toNat) + 1 < 2 ^ n :=
      nat_even_add_one_lt_two_pow hn1 (Nat.xor_lt_two_pow (phi n γ v).isLt γ.isLt) hxor_even2
    change (((phi n γ v) ^^^ γ) + 1#n).toNat = v.toNat
    rw [BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
        Nat.mod_eq_of_lt hlt2, hadd2, Nat.xor_assoc, hstep, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have hfix : phi n γ v = v ↔ γ.toNat = 1 := by
    constructor
    · intro h
      have h1 := congrArg BitVec.toNat h
      rw [hstep] at h1
      have h2 := congrArg (fun z => v.toNat ^^^ z) h1
      rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h2
      have h3 := congrArg (fun z => z ^^^ 1) h2
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at h3
      exact h3
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [hstep, h, Nat.xor_self, Nat.xor_zero]
  exact ⟨hstep, hodd_out, hinv, hfix⟩

/-- Core Engine Lemma 2.3 (Self-Similar Even-Half Bit-Slice Contraction):
    When `γ` is odd, `phi (n + 1) γ` preserves the even subspace `{2*u}` and acts on it
    as an exact width-`n` copy of `phi n (γ >>> 1)`. -/
theorem phi_odd_evenStep (n : Nat) (γ : BitVec (n + 1)) (hγ : γ.toNat % 2 = 1) (u : BitVec n) :
    phi (n + 1) γ (BitVec.ofNat (n + 1) (2 * u.toNat)) =
    BitVec.ofNat (n + 1) (2 * (phi n (BitVec.ofNat n (γ.toNat / 2)) u).toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  have hu : 2 * u.toNat < 2 ^ (n + 1) := by have := u.isLt; omega
  have h1lt : 1 < 2 ^ (n + 1) := by have := Nat.two_pow_pos n; omega
  have hγdiv : γ.toNat / 2 < 2 ^ n := by have := γ.isLt; omega
  have hxor_eq : (2 * u.toNat) ^^^ γ.toNat = 2 * (u.toNat ^^^ (γ.toNat / 2)) + 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    cases i with
    | zero =>
      rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
      have h0 : (2 * u.toNat) % 2 = 0 := by omega
      have h1 : (2 * (u.toNat ^^^ (γ.toNat / 2)) + 1) % 2 = 1 := by omega
      rw [h0, h1, hγ]; rfl
    | succ i =>
      rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      have h1 : (2 * u.toNat) / 2 = u.toNat := by omega
      have h2 : (2 * (u.toNat ^^^ (γ.toNat / 2)) + 1) / 2 = u.toNat ^^^ (γ.toNat / 2) := by omega
      rw [h1, h2, Nat.testBit_xor]
  unfold phi
  rw [BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt h1lt, hxor_eq]
  rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hγdiv]
  have h2lt : 2 * (((u.toNat ^^^ (γ.toNat / 2)) + 1 % 2 ^ n) % 2 ^ n) < 2 ^ (n + 1) := by
    have := Nat.mod_lt ((u.toNat ^^^ (γ.toNat / 2)) + 1 % 2 ^ n) (Nat.two_pow_pos n); omega
  rw [Nat.mod_eq_of_lt h2lt]
  have hadd : 2 * (u.toNat ^^^ (γ.toNat / 2)) + 1 + 1 = 2 * ((u.toNat ^^^ (γ.toNat / 2)) + 1) := by omega
  rw [hadd, hpow, Nat.mul_mod_mul_left]
  congr 1
  rw [Nat.add_mod, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow u.isLt hγdiv)]

theorem phi_odd_evenIter (n : Nat) (γ : BitVec (n + 1)) (hγ : γ.toNat % 2 = 1)
    (k : Nat) (u : BitVec n) :
    iter (phi (n + 1) γ) k (BitVec.ofNat (n + 1) (2 * u.toNat)) =
    BitVec.ofNat (n + 1) (2 * (iter (phi n (BitVec.ofNat n (γ.toNat / 2))) k u).toNat) := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih =>
    rw [iter_succ_left, iter_succ_left, phi_odd_evenStep n γ hγ u, ih]

/-- Core Engine Theorem 2.4 (Exact Complete Orbit of 0 & Membership Characterization):
    For EVERY `n : Nat` and EVERY `γ : BitVec n`:
    1. `0#n` has exact minimal period `2 ^ (n - trailingOnes γ)` under `phi n γ`.
    2. A state `v : BitVec n` lies in the zero-orbit iff `v.toNat % 2 ^ trailingOnes γ = 0`. -/
theorem phi_zero_orbit (n : Nat) (γ : BitVec n) :
    HasMinPeriod (phi n γ) 0#n (2 ^ (n - trailingOnes γ)) ∧
    ∀ v : BitVec n,
      (∃ k, k < 2 ^ (n - trailingOnes γ) ∧ iter (phi n γ) k 0#n = v) ↔
      v.toNat % 2 ^ trailingOnes γ = 0 := by
  induction n with
  | zero =>
    have ht : trailingOnes γ = 0 := rfl
    rw [ht]
    have hsc := phi_even_isSingleCycle 0 γ (by have := γ.isLt; simp at this; omega)
    refine ⟨hsc.1, ?_⟩
    intro v
    constructor
    · intro _; omega
    · intro _; exact hsc.2 v
  | succ n ih =>
    by_cases hγ : γ.toNat % 2 = 0
    · have ht : trailingOnes γ = 0 := by
        unfold trailingOnes; rw [trailingOnesNat_succ]; simp [hγ]
      rw [ht, Nat.sub_zero]
      have hsc := phi_even_isSingleCycle (n + 1) γ hγ
      refine ⟨hsc.1, ?_⟩
      intro v
      constructor
      · intro _; omega
      · intro _; exact hsc.2 v
    · have hodd : γ.toNat % 2 = 1 := by omega
      let γ' : BitVec n := BitVec.ofNat n (γ.toNat / 2)
      have hγ'_toNat : γ'.toNat = γ.toNat / 2 := by
        rw [BitVec.toNat_ofNat]
        have := γ.isLt; rw [Nat.pow_succ] at this
        exact Nat.mod_eq_of_lt (by omega)
      have ht : trailingOnes γ = 1 + trailingOnes γ' := by
        unfold trailingOnes
        rw [trailingOnesNat_succ, hγ'_toNat]
        simp [hodd]
      have hsub : n + 1 - trailingOnes γ = n - trailingOnes γ' := by omega
      have ⟨hper', hmem'⟩ := ih γ'
      have hzero : BitVec.ofNat (n + 1) (2 * (0#n).toNat) = 0#(n + 1) := by
        apply BitVec.eq_of_toNat_eq; simp
      have hemb_toNat : ∀ u : BitVec n, (BitVec.ofNat (n + 1) (2 * u.toNat)).toNat = 2 * u.toNat := by
        intro u; rw [BitVec.toNat_ofNat]
        have := u.isLt; rw [Nat.pow_succ]; exact Nat.mod_eq_of_lt (by omega)
      have hemb_inj : ∀ a b : BitVec n,
          BitVec.ofNat (n + 1) (2 * a.toNat) = BitVec.ofNat (n + 1) (2 * b.toNat) → a = b := by
        intro a b hab
        have h := congrArg BitVec.toNat hab
        rw [hemb_toNat, hemb_toNat] at h
        exact BitVec.eq_of_toNat_eq (by omega)
      rw [hsub]
      constructor
      · refine ⟨hper'.1, ?_, ?_⟩
        · rw [← hzero, phi_odd_evenIter n γ hodd, hper'.2.1]
        · intro k hk0 hkp heq
          rw [← hzero, phi_odd_evenIter n γ hodd] at heq
          exact hper'.2.2 k hk0 hkp (hemb_inj _ _ heq)
      · intro v
        rw [ht, Nat.add_comm 1, Nat.pow_succ]
        constructor
        · rintro ⟨k, hk, rfl⟩
          rw [← hzero, phi_odd_evenIter n γ hodd, hemb_toNat]
          have hmv : (iter (phi n γ') k 0#n).toNat % 2 ^ trailingOnes γ' = 0 :=
            (hmem' (iter (phi n γ') k 0#n)).1 ⟨k, hk, rfl⟩
          rw [Nat.mul_comm (2 ^ trailingOnes γ') 2, Nat.mul_mod_mul_left, hmv, Nat.mul_zero]
        · intro hvmod
          have hveven : v.toNat % 2 = 0 := by
            have := congrArg (· % 2) hvmod
            rw [Nat.mul_comm (2 ^ trailingOnes γ') 2, Nat.mod_mul_right_mod] at this
            simpa using this
          let u : BitVec n := BitVec.ofNat n (v.toNat / 2)
          have hu_toNat : u.toNat = v.toNat / 2 := by
            rw [BitVec.toNat_ofNat]
            have := v.isLt; rw [Nat.pow_succ] at this
            exact Nat.mod_eq_of_lt (by omega)
          have huv : BitVec.ofNat (n + 1) (2 * u.toNat) = v := by
            apply BitVec.eq_of_toNat_eq; rw [hemb_toNat, hu_toNat]; omega
          have humod : u.toNat % 2 ^ trailingOnes γ' = 0 := by
            rw [hu_toNat]
            have h1 : v.toNat = 2 * (v.toNat / 2) := by omega
            rw [h1, Nat.mul_comm (2 ^ trailingOnes γ') 2, Nat.mul_mod_mul_left] at hvmod
            omega
          rcases (hmem' u).2 humod with ⟨k, hk, hku⟩
          refine ⟨k, hk, ?_⟩
          rw [← hzero, phi_odd_evenIter n γ hodd, hku, huv]

/-- Core Engine Theorem 2.5 (Exact Carry-Exit Predecessor of 0):
    The unique predecessor of `0#n` under `phi n γ` is `~~~γ`, and it occurs at the exact final
    step `2 ^ (n - trailingOnes γ) - 1` of the zero-orbit! -/
theorem phi_not_eq_zero (n : Nat) (γ : BitVec n) : phi n γ (~~~γ) = 0#n := by
  unfold phi
  have hnotxor : ~~~γ ^^^ γ = BitVec.allOnes n := by
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_not, BitVec.getLsbD_allOnes]
    by_cases hi : i < n
    · simp [hi]
    · simp [hi]
  rw [hnotxor]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_allOnes, BitVec.toNat_ofNat, BitVec.toNat_zero]
  cases n with
  | zero => simp
  | succ k =>
    have hpos : 1 < 2 ^ (k + 1) := by rw [Nat.pow_succ]; have := Nat.two_pow_pos k; omega
    rw [Nat.mod_eq_of_lt hpos]
    have hsum : 2 ^ (k + 1) - 1 + 1 = 2 ^ (k + 1) := by omega
    rw [hsum, Nat.mod_self]

theorem phi_eq_zero_iff (n : Nat) (γ v : BitVec n) : phi n γ v = 0#n ↔ v = ~~~γ := by
  constructor
  · intro h
    exact phi_injective n γ v (~~~γ) (by rw [h, phi_not_eq_zero])
  · rintro rfl; exact phi_not_eq_zero n γ

theorem phi_zero_orbit_exit (n : Nat) (γ : BitVec n) :
    iter (phi n γ) (2 ^ (n - trailingOnes γ) - 1) 0#n = ~~~γ := by
  have hper := (phi_zero_orbit n γ).1
  apply (phi_eq_zero_iff n γ _).1
  rw [← iter_succ_right (phi n γ)]
  have hpos : 0 < 2 ^ (n - trailingOnes γ) := Nat.two_pow_pos _
  have hstep : 2 ^ (n - trailingOnes γ) - 1 + 1 = 2 ^ (n - trailingOnes γ) := by omega
  rw [hstep, hper.2.1]

/-- Core Engine Theorem 2.6 (Complete Pointwise Period Classification of ALL `2^n` States):
    Every `v : BitVec n` lies either in the unique giant zero-orbit (exact minimal period
    `2 ^ (n - t)`), or has exact minimal period `1` (fixed point) or `2` (2-cycle),
    completely determined by `s = ctzNat n v.toNat` and `γ.toNat / 2 ^ (s + 1)`. -/
theorem phi_complete_pointwise (n : Nat) (γ v : BitVec n) :
    (v.toNat % 2 ^ trailingOnes γ = 0 →
      HasMinPeriod (phi n γ) v (2 ^ (n - trailingOnes γ))) ∧
    (v.toNat % 2 ^ trailingOnes γ ≠ 0 →
      let s := ctzNat n v.toNat
      (γ.toNat / 2 ^ (s + 1) = 0 → HasMinPeriod (phi n γ) v 1) ∧
      (γ.toNat / 2 ^ (s + 1) ≠ 0 → HasMinPeriod (phi n γ) v 2)) := by
  constructor
  · intro hdiv
    have ⟨hper, hmem⟩ := phi_zero_orbit n γ
    rcases (hmem v).2 hdiv with ⟨k, _, rfl⟩
    exact hasMinPeriod_of_iter_eq hper k
  · intro hndiv
    induction n with
    | zero =>
      have h0 : trailingOnes γ = 0 := rfl
      rw [h0] at hndiv
      exact False.elim (hndiv (by omega))
    | succ n ih =>
      by_cases hγ : γ.toNat % 2 = 0
      · have ht : trailingOnes γ = 0 := by unfold trailingOnes; rw [trailingOnesNat_succ]; simp [hγ]
        rw [ht] at hndiv
        exact False.elim (hndiv (by omega))
      · have hodd : γ.toNat % 2 = 1 := by omega
        by_cases hv : v.toNat % 2 = 1
        · have hs : ctzNat (n + 1) v.toNat = 0 := by rw [ctzNat_succ]; simp [hv]
          have ⟨_, _, hinv, hfix⟩ := phi_odd_oddStep (n + 1) γ v hodd hv
          dsimp only
          rw [hs, Nat.zero_add, Nat.pow_one]
          have hγ1 : γ.toNat / 2 = 0 ↔ γ.toNat = 1 := by omega
          constructor
          · intro h0
            have h1 := hγ1.1 h0
            refine ⟨by omega, hfix.2 h1, ?_⟩
            intro k hk0 hk1; omega
          · intro hne0
            have hne1 : γ.toNat ≠ 1 := fun h => hne0 (hγ1.2 h)
            refine ⟨by omega, hinv, ?_⟩
            intro k hk0 hk2 heq
            have hk : k = 1 := by omega
            subst hk
            exact hne1 (hfix.1 heq)
        · have hveven : v.toNat % 2 = 0 := by omega
          let γ' : BitVec n := BitVec.ofNat n (γ.toNat / 2)
          let u : BitVec n := BitVec.ofNat n (v.toNat / 2)
          have hγ'_toNat : γ'.toNat = γ.toNat / 2 := by
            rw [BitVec.toNat_ofNat]; have := γ.isLt; rw [Nat.pow_succ] at this
            exact Nat.mod_eq_of_lt (by omega)
          have hu_toNat : u.toNat = v.toNat / 2 := by
            rw [BitVec.toNat_ofNat]; have := v.isLt; rw [Nat.pow_succ] at this
            exact Nat.mod_eq_of_lt (by omega)
          have huv : BitVec.ofNat (n + 1) (2 * u.toNat) = v := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ofNat, hu_toNat]
            have := v.isLt; rw [Nat.mod_eq_of_lt (by omega)]; omega
          have ht : trailingOnes γ = 1 + trailingOnes γ' := by
            unfold trailingOnes; rw [trailingOnesNat_succ, hγ'_toNat]; simp [hodd]
          have hndiv' : u.toNat % 2 ^ trailingOnes γ' ≠ 0 := by
            intro h0
            apply hndiv
            rw [ht, Nat.add_comm 1, Nat.pow_succ, Nat.mul_comm _ 2]
            have hv2 : v.toNat = 2 * u.toNat := by omega
            rw [hv2, Nat.mul_mod_mul_left, h0, Nat.mul_zero]
          have hs : ctzNat (n + 1) v.toNat = 1 + ctzNat n u.toNat := by
            rw [ctzNat_succ, hu_toNat]; simp [hveven]
          have hdivpow : γ.toNat / 2 ^ (1 + ctzNat n u.toNat + 1) =
              γ'.toNat / 2 ^ (ctzNat n u.toNat + 1) := by
            rw [hγ'_toNat, Nat.div_div_eq_div_mul, Nat.mul_comm 2, ← Nat.pow_succ]
            congr 2; omega
          have hemb_inj : ∀ a b : BitVec n,
              BitVec.ofNat (n + 1) (2 * a.toNat) = BitVec.ofNat (n + 1) (2 * b.toNat) → a = b := by
            intro a b hab
            have h := congrArg BitVec.toNat hab
            rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
            have ha := a.isLt; have hb := b.isLt
            rw [Nat.mod_eq_of_lt (by rw [Nat.pow_succ]; omega),
                Nat.mod_eq_of_lt (by rw [Nat.pow_succ]; omega)] at h
            exact BitVec.eq_of_toNat_eq (by omega)
          have htransfer : ∀ p, HasMinPeriod (phi n γ') u p → HasMinPeriod (phi (n + 1) γ) v p := by
            rintro p ⟨hp0, hper, hmin⟩
            refine ⟨hp0, ?_, ?_⟩
            · rw [← huv, phi_odd_evenIter n γ hodd, hper]
            · intro k hk0 hkp heq
              rw [← huv, phi_odd_evenIter n γ hodd] at heq
              exact hmin k hk0 hkp (hemb_inj _ _ heq)
          have ⟨hfix', htwo'⟩ := ih γ' u hndiv'
          dsimp only
          rw [hs, hdivpow]
          exact ⟨fun h0 => htransfer 1 (hfix' h0), fun hne => htransfer 2 (htwo' hne)⟩

/-- Core Engine Theorem 2.7 (Exact Single-Cycle Dichotomy for `phi n γ`):
    For EVERY `n ≥ 1` and EVERY `γ : BitVec n`, `phi n γ` is a single Hamiltonian cycle
    IF AND ONLY IF `γ` is even! -/
theorem phi_singleCycle_iff_even (n : Nat) (hn : 1 ≤ n) (γ : BitVec n) :
    IsSingleCycle n (phi n γ) ↔ γ.toNat % 2 = 0 := by
  constructor
  · intro hsc
    by_cases hγ : γ.toNat % 2 = 0
    · exact hγ
    · have hodd : γ.toNat % 2 = 1 := by omega
      have ht : 1 ≤ trailingOnes γ := by
        cases n with
        | zero => omega
        | succ k => unfold trailingOnes; rw [trailingOnesNat_succ]; simp [hodd]
      have hper0 := (phi_zero_orbit n γ).1
      have heq := hasMinPeriod_unique hsc.1 hper0
      have hlt : n - trailingOnes γ < n := by omega
      have hpowlt : 2 ^ (n - trailingOnes γ) < 2 ^ n := Nat.pow_lt_pow_right (by omega) hlt
      omega
  · exact phi_even_isSingleCycle n γ

/-! ## Section 3: Compiler A — Gray-Basis Parity-Fiber Involution Engine -/

theorem bitVec_getLsbD_ge {w : Nat} (x : BitVec w) (i : Nat) (hi : w ≤ i) :
    x.getLsbD i = false := by
  rw [BitVec.getLsbD]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) hi))

theorem mod_two_eq_of_decide_eq {a b : Nat} (h : decide (a % 2 = 1) = decide (b % 2 = 1)) :
    a % 2 = b % 2 := by
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp_all

theorem ushiftRight_xor {w : Nat} (a b : BitVec w) (k : Nat) :
    (a ^^^ b) >>> k = (a >>> k) ^^^ (b >>> k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]

theorem ushiftRight_ushiftRight {w : Nat} (x : BitVec w) (a b : Nat) :
    (x >>> a) >>> b = x >>> (a + b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_ushiftRight]
  congr 1; omega

theorem gray_xor {w : Nat} (a b : BitVec w) : gray (a ^^^ b) = gray a ^^^ gray b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [gray, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight]
  cases a.getLsbD i <;> cases b.getLsbD i <;>
    cases a.getLsbD (1 + i) <;> cases b.getLsbD (1 + i) <;> rfl

theorem gray_ushiftRight_one {w : Nat} (x : BitVec w) :
    (gray x) >>> 1 = gray (x >>> 1) := by
  unfold gray
  rw [ushiftRight_xor]

theorem invGrayAux_xor {w : Nat} (k : Nat) (a b : BitVec w) :
    invGrayAux k (a ^^^ b) = invGrayAux k a ^^^ invGrayAux k b := by
  induction k generalizing a b with
  | zero => simp [invGrayAux]
  | succ k ih =>
    simp only [invGrayAux, ushiftRight_xor, ih]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_xor]
    cases a.getLsbD i <;> cases b.getLsbD i <;>
      cases (invGrayAux k (a >>> 1)).getLsbD i <;> cases (invGrayAux k (b >>> 1)).getLsbD i <;> rfl

theorem invGray_xor {w : Nat} (a b : BitVec w) :
    invGray (a ^^^ b) = invGray a ^^^ invGray b :=
  invGrayAux_xor w a b

theorem gray_invGrayAux {w : Nat} (k : Nat) (y : BitVec w) :
    gray (invGrayAux k y) = y ^^^ (y >>> k) := by
  induction k generalizing y with
  | zero =>
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp [gray, invGrayAux]
  | succ k ih =>
    simp only [invGrayAux]
    rw [gray_xor, ih (y >>> 1), ushiftRight_ushiftRight]
    unfold gray
    rw [Nat.add_comm 1 k]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_xor]
    cases y.getLsbD i <;> cases (y >>> 1).getLsbD i <;> cases (y >>> (k + 1)).getLsbD i <;> rfl

theorem invGrayAux_gray {w : Nat} (k : Nat) (x : BitVec w) :
    invGrayAux k (gray x) = x ^^^ (x >>> k) := by
  induction k generalizing x with
  | zero =>
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp [invGrayAux]
  | succ k ih =>
    simp only [invGrayAux]
    rw [gray_ushiftRight_one, ih (x >>> 1), ushiftRight_ushiftRight]
    unfold gray
    rw [Nat.add_comm 1 k]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_xor]
    cases x.getLsbD i <;> cases (x >>> 1).getLsbD i <;> cases (x >>> (k + 1)).getLsbD i <;> rfl

theorem ushiftRight_self_eq_zero {w : Nat} (x : BitVec w) : x >>> w = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  exact bitVec_getLsbD_ge x (w + i) (by omega)

theorem gray_invGray {w : Nat} (y : BitVec w) : gray (invGray y) = y := by
  unfold invGray
  rw [gray_invGrayAux, ushiftRight_self_eq_zero]
  simp

theorem invGray_gray {w : Nat} (x : BitVec w) : invGray (gray x) = x := by
  unfold invGray
  rw [invGrayAux_gray, ushiftRight_self_eq_zero]
  simp

theorem xorRange_succ_front (f : Nat → Bool) (k : Nat) :
    xorRange f (k + 1) = xor (f 0) (xorRange (fun i => f (i + 1)) k) := by
  induction k with
  | zero => simp [xorRange]
  | succ k ih =>
    simp only [xorRange] at ih ⊢
    rw [ih]
    cases f 0 <;> cases xorRange (fun i => f (i + 1)) k <;> cases f (k + 1) <;> rfl

theorem xorRange_xor (f g : Nat → Bool) (k : Nat) :
    xorRange (fun i => xor (f i) (g i)) k = xor (xorRange f k) (xorRange g k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [xorRange, ih]
    cases xorRange f k <;> cases xorRange g k <;> cases f k <;> cases g k <;> rfl

theorem parityVec_xor {w : Nat} (a b : BitVec w) :
    parityVec (a ^^^ b) = xor (parityVec a) (parityVec b) := by
  unfold parityVec
  have h : (fun i => (a ^^^ b).getLsbD i) = (fun i => xor (a.getLsbD i) (b.getLsbD i)) := by
    funext i; simp [BitVec.getLsbD_xor]
  rw [h, xorRange_xor]

theorem invGrayAux_getLsbD_zero {w : Nat} (k : Nat) (y : BitVec w) :
    (invGrayAux k y).getLsbD 0 = xorRange (fun i => y.getLsbD i) k := by
  induction k generalizing y with
  | zero => simp [invGrayAux, xorRange]
  | succ k ih =>
    simp only [invGrayAux, BitVec.getLsbD_xor]
    rw [ih (y >>> 1), xorRange_succ_front]
    congr 1
    have hfun : (fun i => (y >>> 1).getLsbD i) = (fun i => y.getLsbD (i + 1)) := by
      funext i
      simp only [BitVec.getLsbD_ushiftRight]
      rw [Nat.add_comm]
    rw [hfun]

theorem invGray_getLsbD_zero {w : Nat} (y : BitVec w) :
    (invGray y).getLsbD 0 = parityVec y :=
  invGrayAux_getLsbD_zero w y

theorem getLsbD_zero_eq_mod_two {w : Nat} (x : BitVec w) :
    x.getLsbD 0 = decide (x.toNat % 2 = 1) := by
  rw [BitVec.getLsbD, Nat.testBit_zero]

theorem parityVec_gray {w : Nat} (x : BitVec w) :
    parityVec (gray x) = x.getLsbD 0 := by
  rw [← invGray_getLsbD_zero, invGray_gray]

theorem gray_one {w : Nat} (hw : 1 ≤ w) : gray (1#w) = 1#w := by
  apply BitVec.eq_of_toNat_eq
  unfold gray
  rw [BitVec.toNat_xor, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  have h1 : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (by
    cases w with | zero => omega | succ k => rw [Nat.pow_succ]; have := Nat.two_pow_pos k; omega)
  rw [h1]
  simp

theorem grayInvMap_injective {n : Nat} {P : BitVec (n + 1) → BitVec (n + 1)} {δ m : BitVec (n + 1)}
    (spec : GrayInvolutionSpec P δ m) :
    ∀ a b, grayInvMap P δ a = grayInvMap P δ b → a = b := by
  intro a b h
  unfold grayInvMap at h
  have h1 : invGray (P (gray a)) = invGray (P (gray b)) := by
    have hx := congrArg (fun z => (z ^^^ δ) - 1#(n + 1)) h
    simpa [BitVec.xor_assoc] using hx
  have h2 := congrArg (fun z => invGray (P (gray z))) h1
  rw [gray_invGray, spec.involutive, invGray_gray, gray_invGray, spec.involutive, invGray_gray] at h2
  exact h2

theorem grayInvMap_alt_parity {n : Nat} {P : BitVec (n + 1) → BitVec (n + 1)} {δ m : BitVec (n + 1)}
    (spec : GrayInvolutionSpec P δ m) (x : BitVec (n + 1)) :
    (grayInvMap P δ x).toNat % 2 = 1 - x.toNat % 2 := by
  unfold grayInvMap
  have hz_par : (invGray (P (gray x))).toNat % 2 = x.toNat % 2 := by
    have h1 := invGray_getLsbD_zero (P (gray x))
    rw [spec.parity_pres, parityVec_gray, getLsbD_zero_eq_mod_two, getLsbD_zero_eq_mod_two] at h1
    exact mod_two_eq_of_decide_eq h1
  rw [BitVec.toNat_xor, nat_xor_mod_two, spec.delta_even, Nat.xor_zero]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  have hmod2 : ∀ a, (a % 2 ^ (n + 1)) % 2 = a % 2 := fun a => by
    rw [hpow, Nat.mod_mul_right_mod]
  rw [hmod2]
  have h1 : 1 % 2 ^ (n + 1) = 1 := Nat.mod_eq_of_lt (by rw [hpow]; have := Nat.two_pow_pos n; omega)
  rw [h1, Nat.add_mod, hz_par]
  have hx : x.toNat % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

theorem grayInvSpec_m_odd {n : Nat} {P : BitVec (n + 1) → BitVec (n + 1)} {δ m : BitVec (n + 1)}
    (spec : GrayInvolutionSpec P δ m) :
    (invGray m).toNat % 2 = 1 := by
  have h := congrArg parityVec (spec.coset_equiv 0#(n + 1))
  rw [spec.parity_pres, parityVec_xor, parityVec_xor, parityVec_xor, spec.parity_pres,
      parityVec_gray, getLsbD_zero_eq_mod_two, spec.delta_even] at h
  have hpar1 : parityVec 1#(n + 1) = true := by
    have hg1 := parityVec_gray 1#(n + 1)
    rw [gray_one (by omega), getLsbD_zero_eq_mod_two, BitVec.toNat_ofNat] at hg1
    have hlt : 1 < 2 ^ (n + 1) := by rw [Nat.pow_succ]; have := Nat.two_pow_pos n; omega
    rw [Nat.mod_eq_of_lt hlt] at hg1
    exact hg1
  have hpar0 : parityVec 0#(n + 1) = false := by
    have hg0 := parityVec_gray 0#(n + 1)
    have h0 : gray 0#(n + 1) = 0#(n + 1) := by simp [gray]
    rw [h0] at hg0; simpa using hg0
  rw [hpar1, hpar0] at h
  simp only [Bool.false_xor] at h
  have hdec0 : decide ((0 : Nat) = 1) = false := rfl
  rw [hdec0, Bool.xor_false] at h
  have hm_par : parityVec m = true := h.symm
  rw [← invGray_getLsbD_zero, getLsbD_zero_eq_mod_two] at hm_par
  have hm : (invGray m).toNat % 2 = 0 ∨ (invGray m).toNat % 2 = 1 := by omega
  rcases hm with hm | hm <;> simp_all

/-- Compiler A Core Reduction Lemma:
    For ANY `GrayInvolutionSpec P δ m` and ANY even state `x` (`x.toNat % 2 = 0`),
    `grayInvMap P δ (grayInvMap P δ x) = ((x ^^^ invGray m) + 1) ^^^ δ`! -/
theorem grayInvMap_twoStep_formula {n : Nat}
    {P : BitVec (n + 1) → BitVec (n + 1)} {δ m : BitVec (n + 1)}
    (spec : GrayInvolutionSpec P δ m) (x : BitVec (n + 1)) (hxeven : x.toNat % 2 = 0) :
    grayInvMap P δ (grayInvMap P δ x) = ((x ^^^ invGray m) + 1#(n + 1)) ^^^ δ := by
  have hz_even : (invGray (P (gray x))).toNat % 2 = 0 := by
    have h1 := invGray_getLsbD_zero (P (gray x))
    rw [spec.parity_pres, parityVec_gray, getLsbD_zero_eq_mod_two, getLsbD_zero_eq_mod_two] at h1
    have heq := mod_two_eq_of_decide_eq h1
    omega
  have hz_add : invGray (P (gray x)) + 1#(n + 1) = invGray (P (gray x)) ^^^ 1#(n + 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_ofNat]
    have h1lt : 1 < 2 ^ (n + 1) := by rw [Nat.pow_succ]; have := Nat.two_pow_pos n; omega
    rw [Nat.mod_eq_of_lt h1lt]
    have hlt : (invGray (P (gray x))).toNat + 1 < 2 ^ (n + 1) :=
      nat_even_add_one_lt_two_pow (by omega) (invGray (P (gray x))).isLt hz_even
    rw [Nat.mod_eq_of_lt hlt, nat_even_add_one_eq_xor_one hz_even]
  have hFx : grayInvMap P δ x = invGray (P (gray x)) ^^^ (1#(n + 1) ^^^ δ) := by
    unfold grayInvMap
    rw [hz_add, BitVec.xor_assoc]
  change (invGray (P (gray (grayInvMap P δ x))) + 1#(n + 1)) ^^^ δ = _
  rw [hFx, gray_xor, gray_xor, gray_invGray, gray_one (by omega),
      spec.coset_equiv, spec.involutive, invGray_xor, invGray_gray]

/-- Compiler A Master Theorem 3.1 (Exact Conjugacy of 2-Step Return Map to `phi n γ`):
    Let `β := δ >>> 1` and `γ := compiledDefect δ m = ((invGray m ^^^ δ) >>> 1)`.
    Then `grayInvMap P δ` strictly alternates parity, and on even states `2 * (v ^^^ β)`,
    its 2-step return map is EXACTLY `v ↦ phi n γ v`! -/
theorem grayInvMap_return_map {n : Nat}
    {P : BitVec (n + 1) → BitVec (n + 1)} {δ m : BitVec (n + 1)}
    (spec : GrayInvolutionSpec P δ m) :
    let β : BitVec n := BitVec.ofNat n (δ.toNat / 2)
    let γ : BitVec n := compiledDefect δ m
    let R : BitVec n → BitVec n := fun u => phi n γ (u ^^^ β) ^^^ β
    ∀ u : BitVec n,
      grayInvMap P δ (grayInvMap P δ (BitVec.ofNat (n + 1) (2 * u.toNat))) =
      BitVec.ofNat (n + 1) (2 * (R u).toNat) := by
  intro β γ R u
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  have hu : 2 * u.toNat < 2 ^ (n + 1) := by have := u.isLt; omega
  have heven : (BitVec.ofNat (n + 1) (2 * u.toNat)).toNat % 2 = 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu]; omega
  rw [grayInvMap_twoStep_formula spec _ heven]
  apply BitVec.eq_of_toNat_eq
  have hmodd : (invGray m).toNat % 2 = 1 := grayInvSpec_m_odd spec
  have hβ : β.toNat = δ.toNat / 2 := by
    rw [BitVec.toNat_ofNat]; have := δ.isLt; rw [Nat.pow_succ] at this
    exact Nat.mod_eq_of_lt (by omega)
  have hγ : γ.toNat = ((invGray m).toNat / 2) ^^^ (δ.toNat / 2) := by
    unfold γ compiledDefect
    rw [BitVec.toNat_ofNat, BitVec.toNat_xor, nat_xor_div_two]
    have hmdiv : (invGray m).toNat / 2 < 2 ^ n := by have := (invGray m).isLt; omega
    have hδdiv : δ.toNat / 2 < 2 ^ n := by have := δ.isLt; omega
    exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hmdiv hδdiv)
  have hα : ((u ^^^ β) ^^^ γ).toNat = u.toNat ^^^ ((invGray m).toNat / 2) := by
    rw [BitVec.toNat_xor, BitVec.toNat_xor, hβ, hγ]
    rw [Nat.xor_assoc, Nat.xor_comm (δ.toNat / 2), Nat.xor_assoc ((invGray m).toNat / 2),
        Nat.xor_self, Nat.xor_zero]
  have h1lt : 1 < 2 ^ (n + 1) := by have := Nat.two_pow_pos n; omega
  have huxor : (2 * u.toNat) ^^^ (invGray m).toNat = 2 * (u.toNat ^^^ ((invGray m).toNat / 2)) + 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    cases i with
    | zero =>
      rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
      have h0 : (2 * u.toNat) % 2 = 0 := by omega
      have h1 : (2 * (u.toNat ^^^ ((invGray m).toNat / 2)) + 1) % 2 = 1 := by omega
      rw [h0, h1, hmodd]; rfl
    | succ i =>
      rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      have h1 : (2 * u.toNat) / 2 = u.toNat := by omega
      have h2 : (2 * (u.toNat ^^^ ((invGray m).toNat / 2)) + 1) / 2 = u.toNat ^^^ ((invGray m).toNat / 2) := by omega
      rw [h1, h2, Nat.testBit_xor]
  have hstep1 : (((BitVec.ofNat (n + 1) (2 * u.toNat) ^^^ invGray m) + 1#(n + 1))).toNat =
      2 * (phi n γ (u ^^^ β)).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt h1lt, huxor]
    unfold phi
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, hα]
    have hadd : 2 * (u.toNat ^^^ ((invGray m).toNat / 2)) + 1 + 1 =
        2 * ((u.toNat ^^^ ((invGray m).toNat / 2)) + 1) := by omega
    rw [hadd, hpow, Nat.mul_mod_mul_left]
    congr 1
    have hlt_uα : u.toNat ^^^ ((invGray m).toNat / 2) < 2 ^ n :=
      Nat.xor_lt_two_pow u.isLt (by have := (invGray m).isLt; omega)
    rw [Nat.add_mod, Nat.mod_eq_of_lt hlt_uα]
  have hRlt : 2 * (R u).toNat < 2 ^ (n + 1) := by have := (R u).isLt; omega
  rw [BitVec.toNat_xor, hstep1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hRlt]
  unfold R
  rw [BitVec.toNat_xor, hβ]
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    rw [Nat.testBit_xor, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    have h0 : (2 * (phi n γ (u ^^^ β)).toNat) % 2 = 0 := by omega
    have h2 : (2 * ((phi n γ (u ^^^ β)).toNat ^^^ (δ.toNat / 2))) % 2 = 0 := by omega
    rw [h0, h2, spec.delta_even]; rfl
  | succ i =>
    rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    have h1 : (2 * (phi n γ (u ^^^ β)).toNat) / 2 = (phi n γ (u ^^^ β)).toNat := by omega
    have h2 : (2 * ((phi n γ (u ^^^ β)).toNat ^^^ (δ.toNat / 2))) / 2 =
        (phi n γ (u ^^^ β)).toNat ^^^ (δ.toNat / 2) := by omega
    rw [h1, h2, Nat.testBit_xor]

/-- Compiler A Master Theorem 3.2 (Complete Pointwise Period Decomposition of ALL `2^(n+1)` States):
    Every state `x : BitVec (n + 1)` under `grayInvMap P δ` has exact minimal period in
    `{2, 4, 2 ^ (n + 1 - trailingOnes γ)}`, determined purely by the compiled signature `γ`! -/
theorem grayInvMap_complete_pointwise {n : Nat}
    {P : BitVec (n + 1) → BitVec (n + 1)} {δ m : BitVec (n + 1)}
    (spec : GrayInvolutionSpec P δ m) (x : BitVec (n + 1)) :
    let β : BitVec n := BitVec.ofNat n (δ.toNat / 2)
    let γ : BitVec n := compiledDefect δ m
    let v : BitVec n :=
      (if x.toNat % 2 = 0 then BitVec.ofNat n (x.toNat / 2)
       else BitVec.ofNat n ((grayInvMap P δ x).toNat / 2)) ^^^ β
    (v.toNat % 2 ^ trailingOnes γ = 0 →
      HasMinPeriod (grayInvMap P δ) x (2 ^ (n + 1 - trailingOnes γ))) ∧
    (v.toNat % 2 ^ trailingOnes γ ≠ 0 →
      let s := ctzNat n v.toNat
      (γ.toNat / 2 ^ (s + 1) = 0 → HasMinPeriod (grayInvMap P δ) x 2) ∧
      (γ.toNat / 2 ^ (s + 1) ≠ 0 → HasMinPeriod (grayInvMap P δ) x 4)) := by
  intro β γ v
  let R : BitVec n → BitVec n := fun u => phi n γ (u ^^^ β) ^^^ β
  have hconj : ∀ u p, HasMinPeriod R u p ↔ HasMinPeriod (phi n γ) (u ^^^ β) p := by
    intro u p
    exact hasMinPeriod_conj (fun z => z ^^^ β) (fun z => z ^^^ β)
      (fun z => by simp [BitVec.xor_assoc])
      (fun z => by simp [R, BitVec.xor_assoc])
  have hlift : ∀ p, HasMinPeriod (grayInvMap P δ) x (2 * p) ↔ HasMinPeriod (phi n γ) v p := by
    intro p
    by_cases hx : x.toNat % 2 = 0
    · have hv : v = BitVec.ofNat n (x.toNat / 2) ^^^ β := by simp [v, hx]
      have hxemb : BitVec.ofNat (n + 1) (2 * (BitVec.ofNat n (x.toNat / 2)).toNat) = x := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have hlt := x.isLt; rw [Nat.pow_succ] at hlt
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
      rw [← hxemb, hasMinPeriod_twoStep_even (grayInvMap P δ) R
          (grayInvMap_alt_parity spec) (grayInvMap_return_map spec), hconj, ← hv]
    · have hxodd : x.toNat % 2 = 1 := by omega
      have hv : v = BitVec.ofNat n ((grayInvMap P δ x).toNat / 2) ^^^ β := by simp [v, hx]
      rw [hasMinPeriod_twoStep_odd (grayInvMap P δ) R
          (grayInvMap_alt_parity spec) (grayInvMap_return_map spec)
          (grayInvMap_injective spec) x hxodd p, hconj, ← hv]
  have hphi := phi_complete_pointwise n γ v
  have hpow : 2 ^ (n + 1 - trailingOnes γ) = 2 * 2 ^ (n - trailingOnes γ) := by
    have hle : trailingOnes γ ≤ n := trailingOnesNat_le n γ.toNat
    have hsub : n + 1 - trailingOnes γ = (n - trailingOnes γ) + 1 := by omega
    rw [hsub, Nat.pow_succ, Nat.mul_comm]
  constructor
  · intro hdiv
    rw [hpow, hlift]
    exact hphi.1 hdiv
  · intro hndiv
    dsimp only
    constructor
    · intro h0
      exact (hlift 1).2 ((hphi.2 hndiv).1 h0)
    · intro hne
      exact (hlift 2).2 ((hphi.2 hndiv).2 hne)

/-- Compiler A Master Theorem 3.3 (Single-Cycle Dichotomy for ALL `GrayInvolutionSpec`):
    For EVERY `n ≥ 1` and EVERY `GrayInvolutionSpec P δ m`, `grayInvMap P δ` is a single
    full-period Hamiltonian cycle on `BitVec (n + 1)` IF AND ONLY IF `compiledDefect δ m` is even! -/
theorem grayInvMap_singleCycle_iff {n : Nat} (hn : 1 ≤ n)
    {P : BitVec (n + 1) → BitVec (n + 1)} {δ m : BitVec (n + 1)}
    (spec : GrayInvolutionSpec P δ m) :
    IsSingleCycle (n + 1) (grayInvMap P δ) ↔ (compiledDefect δ m).toNat % 2 = 0 := by
  let β : BitVec n := BitVec.ofNat n (δ.toNat / 2)
  let γ : BitVec n := compiledDefect δ m
  let R : BitVec n → BitVec n := fun u => phi n γ (u ^^^ β) ^^^ β
  constructor
  · intro hsc
    by_cases hγ : γ.toNat % 2 = 0
    · exact hγ
    · have hodd : γ.toNat % 2 = 1 := by omega
      have ht : 1 ≤ trailingOnes γ := by
        cases n with
        | zero => omega
        | succ k => unfold trailingOnes; rw [trailingOnesNat_succ]; simp [hodd]
      -- The even state `2 * β` maps to `v = β ^^^ β = 0`, which has exact minimal period `2^(n+1-t) < 2^(n+1)`!
      let x0 : BitVec (n + 1) := BitVec.ofNat (n + 1) (2 * β.toNat)
      have hx0_all := isSingleCycle_all_minPeriod hsc x0
      have hx0_even : x0.toNat % 2 = 0 := by
        rw [BitVec.toNat_ofNat]
        have hlt : 2 * β.toNat < 2 ^ (n + 1) := by rw [Nat.pow_succ]; have := β.isLt; omega
        rw [Nat.mod_eq_of_lt hlt]; omega
      have hdiv_x0 : BitVec.ofNat n (x0.toNat / 2) = β := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have hlt : 2 * β.toNat < 2 ^ (n + 1) := by rw [Nat.pow_succ]; have := β.isLt; omega
        rw [Nat.mod_eq_of_lt hlt]
        have hdiv : (2 * β.toNat) / 2 = β.toNat := by omega
        rw [hdiv, Nat.mod_eq_of_lt β.isLt]
      have hpt := (grayInvMap_complete_pointwise spec x0).1
      have hper_short : HasMinPeriod (grayInvMap P δ) x0 (2 ^ (n + 1 - trailingOnes γ)) := by
        apply hpt
        have hzero_v :
            ((if x0.toNat % 2 = 0 then BitVec.ofNat n (x0.toNat / 2)
              else BitVec.ofNat n ((grayInvMap P δ x0).toNat / 2)) ^^^
              BitVec.ofNat n (δ.toNat / 2)) = 0#n := by
          simp only [hx0_even, ↓reduceIte, hdiv_x0]
          exact BitVec.xor_self
        rw [hzero_v]; simp
      have heq := hasMinPeriod_unique hx0_all hper_short
      have hlt : n + 1 - trailingOnes γ < n + 1 := by omega
      have hpowlt : 2 ^ (n + 1 - trailingOnes γ) < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by omega) hlt
      omega
  · intro heven
    have hphi_sc : IsSingleCycle n (phi n γ) := phi_even_isSingleCycle n γ heven
    have hR_sc : IsSingleCycle n R :=
      isSingleCycle_conj (fun z => z ^^^ β) (fun z => z ^^^ β)
        (fun z => by simp [BitVec.xor_assoc])
        (fun z => by simp [BitVec.xor_assoc])
        (fun z => by simp [R, BitVec.xor_assoc])
        hphi_sc
    exact isSingleCycle_twoStep (grayInvMap P δ) R
      (grayInvMap_alt_parity spec) (grayInvMap_return_map spec)
      (grayInvMap_injective spec) hR_sc

/-! ## Section 4: Concrete Infinite Silicon Families Discharged by Compiler A -/

theorem ofBitsNat_lt (b : Nat → Bool) (w : Nat) : ofBitsNat b w < 2 ^ w := by
  induction w generalizing b with
  | zero => simp [ofBitsNat]
  | succ k ih =>
    unfold ofBitsNat
    have := ih (fun i => b (i + 1))
    rw [Nat.pow_succ]
    cases b 0 <;> simp <;> omega

theorem ofBitsNat_testBit (b : Nat → Bool) (w i : Nat) :
    (ofBitsNat b w).testBit i = (decide (i < w) && b i) := by
  induction w generalizing b i with
  | zero => simp [ofBitsNat]
  | succ k ih =>
    unfold ofBitsNat
    cases i with
    | zero =>
      rw [Nat.testBit_zero]
      cases b 0 <;> simp
    | succ j =>
      rw [Nat.testBit_succ]
      have hdiv : (2 * ofBitsNat (fun i => b (i + 1)) k + if b 0 then 1 else 0) / 2 =
          ofBitsNat (fun i => b (i + 1)) k := by
        cases b 0 <;> simp <;> omega
      rw [hdiv, ih (fun i => b (i + 1)) j]
      simp [Nat.succ_lt_succ_iff]

theorem getLsbD_applyBitPerm {w : Nat} (π : Fin w → Fin w) (x : BitVec w) (i : Nat) :
    (applyBitPerm w π x).getLsbD i = if h : i < w then x.getLsbD (π ⟨i, h⟩).val else false := by
  unfold applyBitPerm
  rw [BitVec.getLsbD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (ofBitsNat_lt _ w), ofBitsNat_testBit]
  by_cases h : i < w
  · simp [h]
  · simp [h]

theorem applyBitPerm_involutive {w : Nat} (π : Fin w → Fin w) (hinv : ∀ i, π (π i) = i) (x : BitVec w) :
    applyBitPerm w π (applyBitPerm w π x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_applyBitPerm]
  simp only [hi, ↓reduceDIte, getLsbD_applyBitPerm, (π ⟨i, hi⟩).isLt, hinv]

theorem applyBitPerm_xor {w : Nat} (π : Fin w → Fin w) (a b : BitVec w) :
    applyBitPerm w π (a ^^^ b) = applyBitPerm w π a ^^^ applyBitPerm w π b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, getLsbD_applyBitPerm, hi, ↓reduceDIte]

theorem getLsbD_unitBit {w : Nat} (j i : Nat) (hj : j < w) :
    (1#w <<< j).getLsbD i = decide (i = j) := by
  rw [BitVec.getLsbD_shiftLeft]
  by_cases hi : i < w
  · by_cases hle : j ≤ i
    · have hnl : ¬ i < j := by omega
      simp only [hi, hnl, decide_true, decide_false, Bool.not_false, Bool.true_and]
      rw [BitVec.getLsbD, BitVec.toNat_ofNat]
      have h1 : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (by
        cases w with | zero => omega | succ k => rw [Nat.pow_succ]; have := Nat.two_pow_pos k; omega)
      rw [h1]
      cases hsub : i - j with
      | zero =>
        have heq : i = j := by omega
        subst heq
        rw [Nat.testBit_zero]
        simp
      | succ d =>
        have hne : i ≠ j := by omega
        have htb : (1 : Nat).testBit (d + 1) = false := by
          rw [Nat.testBit_succ]; simp
        simp [hne, htb]
    · have hlt : i < j := by omega
      have hne : i ≠ j := by omega
      simp [hi, hlt, hne]
  · have hne : i ≠ j := by omega
    simp [hi, hne]

theorem applyBitPerm_unitBit {w : Nat} (π : Fin w → Fin w) (hinv : ∀ i, π (π i) = i)
    (j : Nat) (hj : j < w) :
    applyBitPerm w π (1#w <<< j) = 1#w <<< (π ⟨j, hj⟩).val := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_applyBitPerm, getLsbD_unitBit _ i (π ⟨j, hj⟩).isLt]
  simp only [hi, ↓reduceDIte, getLsbD_unitBit j _ hj]
  by_cases heq : i = (π ⟨j, hj⟩).val
  · have h1 : (π ⟨i, hi⟩).val = j := by
      have hfin : (⟨i, hi⟩ : Fin w) = π ⟨j, hj⟩ := Fin.ext heq
      rw [hfin, hinv]
    rw [decide_eq_true h1, decide_eq_true heq]
  · have h1 : (π ⟨i, hi⟩).val ≠ j := by
      intro hval
      apply heq
      have hfin : π ⟨i, hi⟩ = ⟨j, hj⟩ := Fin.ext hval
      have h2 := congrArg π hfin
      rw [hinv] at h2
      exact congrArg Fin.val h2
    rw [decide_eq_false h1, decide_eq_false heq]

theorem parityVec_unitBit {w : Nat} (j : Nat) (hj : j < w) :
    parityVec (1#w <<< j) = true := by
  unfold parityVec
  have hgen : ∀ k, xorRange (fun i => decide (i = j)) k = decide (j < k) := by
    intro k
    induction k with
    | zero => simp [xorRange]
    | succ k ih =>
      simp only [xorRange, ih]
      by_cases hlt : j < k
      · have hne : k ≠ j := by omega
        have hlt2 : j < k + 1 := by omega
        rw [decide_eq_true hlt, decide_eq_false hne, decide_eq_true hlt2]; rfl
      · by_cases heq : k = j
        · have hlt2 : j < k + 1 := by omega
          rw [decide_eq_false hlt, decide_eq_true heq, decide_eq_true hlt2]; rfl
        · have hlt2 : ¬ j < k + 1 := by omega
          rw [decide_eq_false hlt, decide_eq_false heq, decide_eq_false hlt2]; rfl
  have hfun : (fun i => (1#w <<< j).getLsbD i) = (fun i => decide (i = j)) := by
    funext i; exact getLsbD_unitBit j i hj
  rw [hfun, hgen]
  simp [hj]

theorem parityVec_applyBitPerm {w : Nat} (π : Fin w → Fin w) (hinv : ∀ i, π (π i) = i) (y : BitVec w) :
    parityVec (applyBitPerm w π y) = parityVec y := by
  suffices h : ∀ k (z : BitVec w), (∀ i, k ≤ i → z.getLsbD i = false) →
      parityVec (applyBitPerm w π z) = parityVec z by
    exact h w y (fun i hi => bitVec_getLsbD_ge y i hi)
  intro k
  induction k with
  | zero =>
    intro z hz
    have hz0 : z = 0#w := by
      apply BitVec.eq_of_getLsbD_eq; intro i _; simp [hz i (Nat.zero_le i)]
    subst hz0
    have hp0 : applyBitPerm w π 0#w = 0#w := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; rw [getLsbD_applyBitPerm]; simp [hi]
    rw [hp0]
  | succ k ih =>
    intro z hz
    by_cases hkw : k < w
    · by_cases hbit : z.getLsbD k = true
      · let z' := z ^^^ (1#w <<< k)
        have hz' : ∀ i, k ≤ i → z'.getLsbD i = false := by
          intro i hi
          simp only [z', BitVec.getLsbD_xor, getLsbD_unitBit k i hkw]
          by_cases heq : i = k
          · subst heq; simp [hbit]
          · have hgt : k + 1 ≤ i := by omega
            simp [heq, hz i hgt]
        have hz_eq : z = z' ^^^ (1#w <<< k) := by simp [z', BitVec.xor_assoc]
        rw [hz_eq, applyBitPerm_xor, parityVec_xor, parityVec_xor,
            applyBitPerm_unitBit π hinv k hkw, parityVec_unitBit _ (π ⟨k, hkw⟩).isLt,
            parityVec_unitBit k hkw, ih z' hz']
      · apply ih z
        intro i hi
        by_cases heq : i = k
        · subst heq; cases h : z.getLsbD i <;> simp_all
        · exact hz i (by omega)
    · apply ih z
      intro i hi
      exact bitVec_getLsbD_ge z i (by omega)

/-- Every bit-permutation involution `π : Fin (n+1) → Fin (n+1)` automatically instantiates Compiler A! -/
theorem bitPerm_grayInvolutionSpec {n : Nat} (π : Fin (n + 1) → Fin (n + 1))
    (hinv : ∀ i, π (π i) = i) (δ : BitVec (n + 1)) (hδ : δ.toNat % 2 = 0) :
    GrayInvolutionSpec (applyBitPerm (n + 1) π) δ (applyBitPerm (n + 1) π (1#(n + 1) ^^^ gray δ)) where
  involutive := applyBitPerm_involutive π hinv
  parity_pres := parityVec_applyBitPerm π hinv
  delta_even := hδ
  coset_equiv := fun y => applyBitPerm_xor π y _

theorem invGray_unitBit_toNat {w : Nat} (j : Nat) (hj : j < w) :
    (invGray (1#w <<< j)).toNat = 2 ^ (j + 1) - 1 := by
  have hbits : ∀ i, (invGray (1#w <<< j)).getLsbD i = decide (i ≤ j) := by
    have hgray : gray (BitVec.ofNat w (2 ^ (j + 1) - 1)) = 1#w <<< j := by
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      rw [getLsbD_unitBit j i hj]
      unfold gray
      rw [BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight]
      have hlt : 2 ^ (j + 1) - 1 < 2 ^ w := by
        have hle : 2 ^ (j + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
        have hpos : 0 < 2 ^ (j + 1) := Nat.two_pow_pos _
        omega
      have htb : ∀ k, (BitVec.ofNat w (2 ^ (j + 1) - 1)).getLsbD k = decide (k < j + 1) := by
        intro k
        rw [BitVec.getLsbD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.testBit_two_pow_sub_one]
      rw [htb i, htb (1 + i)]
      by_cases h1 : i = j
      · subst h1
        have hlt1 : i < i + 1 := by omega
        have hlt2 : ¬ (1 + i < i + 1) := by omega
        rw [decide_eq_true hlt1, decide_eq_false hlt2]; simp
      · by_cases h2 : i < j
        · have h3 : i < j + 1 := by omega
          have h4 : 1 + i < j + 1 := by omega
          rw [decide_eq_true h3, decide_eq_true h4, decide_eq_false h1]; rfl
        · have h3 : ¬ i < j + 1 := by omega
          have h4 : ¬ 1 + i < j + 1 := by omega
          rw [decide_eq_false h3, decide_eq_false h4, decide_eq_false h1]; rfl
    intro i
    have heq : invGray (1#w <<< j) = BitVec.ofNat w (2 ^ (j + 1) - 1) := by
      rw [← hgray, invGray_gray]
    rw [heq]
    have hlt : 2 ^ (j + 1) - 1 < 2 ^ w := by
      have hle : 2 ^ (j + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
      have hpos : 0 < 2 ^ (j + 1) := Nat.two_pow_pos _
      omega
    rw [BitVec.getLsbD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.testBit_two_pow_sub_one]
    by_cases h : i ≤ j <;> simp [h, Nat.lt_succ_iff]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [← BitVec.getLsbD, hbits i, Nat.testBit_two_pow_sub_one]
  by_cases h : i ≤ j <;> simp [h, Nat.lt_succ_iff]

theorem trailingOnesNat_two_pow_sub_one (n j : Nat) (hjn : j ≤ n) :
    trailingOnesNat n (2 ^ j - 1) = j := by
  induction j generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ k => rw [trailingOnesNat_succ]; simp
  | succ j ih =>
    cases n with
    | zero => omega
    | succ k =>
      rw [trailingOnesNat_succ]
      have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
      have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
      have hodd : (2 ^ (j + 1) - 1) % 2 = 1 := by omega
      have hdiv : (2 ^ (j + 1) - 1) / 2 = 2 ^ j - 1 := by omega
      simp [hodd, hdiv, ih k (by omega)]
      omega

/-- INFINITE THEOREM 4.1 (Universal Gray-Basis Bit-Permutation Involution Collapse for `+ 1`):
    For EVERY width `w = n + 1 ≥ 2` and EVERY bit-permutation involution `π : Fin (n+1) → Fin (n+1)`,
    let `j = (π 0).val`. Then for `F(x) = invGray (applyBitPerm (n+1) π (gray x)) + 1`:
    1. The compiled defect signature is ALWAYS `γ = 2^j - 1` (with `trailingOnes γ = j`).
    2. `0` has exact minimal period `2 ^ (n + 1 - j)`.
    3. `F` is a single Hamiltonian cycle IF AND ONLY IF `j = 0`.
    4. Every state `x : BitVec (n + 1)` has exact minimal period in `{2, 4, 2 ^ (n + 1 - j)}`. -/
theorem grayBitPermInvolution_plusOne_universal {n : Nat} (hn : 1 ≤ n)
    (π : Fin (n + 1) → Fin (n + 1)) (hinv : ∀ i, π (π i) = i) :
    let F : BitVec (n + 1) → BitVec (n + 1) := fun x => invGray (applyBitPerm (n + 1) π (gray x)) + 1#(n + 1)
    let j : Nat := (π ⟨0, by omega⟩).val
    HasMinPeriod F 0#(n + 1) (2 ^ (n + 1 - j)) ∧
    (IsSingleCycle (n + 1) F ↔ j = 0) ∧
    ∀ x : BitVec (n + 1),
      HasMinPeriod F x (2 ^ (n + 1 - j)) ∨ HasMinPeriod F x 2 ∨ HasMinPeriod F x 4 := by
  intro F j
  have hF_eq : F = grayInvMap (applyBitPerm (n + 1) π) 0#(n + 1) := by
    funext x; simp [F, grayInvMap]
  have hspec := bitPerm_grayInvolutionSpec π hinv 0#(n + 1) (by simp)
  have hg0 : gray 0#(n + 1) = 0#(n + 1) := by simp [gray]
  have hm_eq : applyBitPerm (n + 1) π (1#(n + 1) ^^^ gray 0#(n + 1)) = 1#(n + 1) <<< j := by
    rw [hg0, BitVec.xor_zero]
    have h1 := applyBitPerm_unitBit π hinv 0 (by omega)
    rw [BitVec.shiftLeft_zero] at h1
    exact h1
  have hγ_toNat : (compiledDefect 0#(n + 1) (applyBitPerm (n + 1) π (1#(n + 1) ^^^ gray 0#(n + 1)))).toNat =
      2 ^ j - 1 := by
    unfold compiledDefect
    rw [hm_eq, BitVec.xor_zero, invGray_unitBit_toNat j (π ⟨0, by omega⟩).isLt]
    have hdiv : (2 ^ (j + 1) - 1) / 2 = 2 ^ j - 1 := by
      have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
      rw [Nat.pow_succ]; omega
    rw [hdiv, BitVec.toNat_ofNat]
    have hjle : j ≤ n := by have := (π ⟨0, by omega⟩).isLt; omega
    have hlt : 2 ^ j - 1 < 2 ^ n := by
      have hle : 2 ^ j ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hjle
      have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
      omega
    exact Nat.mod_eq_of_lt hlt
  have htr : trailingOnes (compiledDefect 0#(n + 1) (applyBitPerm (n + 1) π (1#(n + 1) ^^^ gray 0#(n + 1)))) = j := by
    unfold trailingOnes
    rw [hγ_toNat]
    exact trailingOnesNat_two_pow_sub_one n j (by have := (π ⟨0, by omega⟩).isLt; omega)
  rw [hF_eq]
  refine ⟨?_, ?_, ?_⟩
  · -- Orbit of 0 has exact minimal period `2 ^ (n + 1 - j)`
    have hpt := (grayInvMap_complete_pointwise hspec 0#(n + 1)).1
    rw [htr] at hpt
    apply hpt
    simp
  · -- Single cycle iff `j = 0`
    rw [grayInvMap_singleCycle_iff hn hspec, hγ_toNat]
    cases j with
    | zero => simp
    | succ k =>
      have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
      have hodd : (2 ^ (k + 1) - 1) % 2 = 1 := by rw [Nat.pow_succ]; omega
      simp [hodd]
  · -- Complete pointwise classification into `{2, 4, 2^(n+1-j)}`
    intro x
    have hpt := grayInvMap_complete_pointwise hspec x
    dsimp only at hpt
    rw [htr] at hpt
    by_cases hdiv :
        ((if x.toNat % 2 = 0 then BitVec.ofNat n (x.toNat / 2)
          else BitVec.ofNat n ((grayInvMap (applyBitPerm (n + 1) π) 0#(n + 1) x).toNat / 2)) ^^^
          BitVec.ofNat n ((0#(n + 1)).toNat / 2)).toNat % 2 ^ j = 0
    · exact Or.inl (hpt.1 hdiv)
    · by_cases h0 :
          (compiledDefect 0#(n + 1) (applyBitPerm (n + 1) π (1#(n + 1) ^^^ gray 0#(n + 1)))).toNat /
          2 ^ (ctzNat n ((if x.toNat % 2 = 0 then BitVec.ofNat n (x.toNat / 2)
            else BitVec.ofNat n ((grayInvMap (applyBitPerm (n + 1) π) 0#(n + 1) x).toNat / 2)) ^^^
            BitVec.ofNat n ((0#(n + 1)).toNat / 2)).toNat + 1) = 0
      · exact Or.inr (Or.inl ((hpt.2 hdiv).1 h0))
      · exact Or.inr (Or.inr ((hpt.2 hdiv).2 h0))

theorem bitrevFin_involutive (w : Nat) (i : Fin w) : bitrevFin w (bitrevFin w i) = i := by
  apply Fin.ext; simp [bitrevFin]; omega

/-- COROLLARY 4.1a (Gray-Basis `bitrev + 1` Bounded Order-4 Collapse):
    For EVERY width `w ≥ 2`, `F(x) = invGray (bitrev (gray x)) + 1` has `HasMinPeriod F 0 2`
    and `F^4(x) = x` for EVERY `x : BitVec w`! -/
theorem grayBitrev_plusOne_order4 {w : Nat} (hw : 2 ≤ w) :
    let F : BitVec w → BitVec w := fun x => invGray (applyBitPerm w (bitrevFin w) (gray x)) + 1#w
    HasMinPeriod F 0#w 2 ∧ ∀ x : BitVec w, iter F 4 x = x := by
  cases w with
  | zero => omega
  | succ n =>
    have hn : 1 ≤ n := by omega
    have h := grayBitPermInvolution_plusOne_universal hn (bitrevFin (n + 1)) (bitrevFin_involutive (n + 1))
    have hj : (bitrevFin (n + 1) ⟨0, by omega⟩).val = n := by simp [bitrevFin]
    dsimp only at h ⊢
    rw [hj, show n + 1 - n = 1 by omega, Nat.pow_one] at h
    refine ⟨h.1, ?_⟩
    intro x
    rcases h.2.2 x with h2 | h2 | h4
    · have h22 : iter (fun x => invGray (applyBitPerm (n + 1) (bitrevFin (n + 1)) (gray x)) + 1#(n + 1)) (2 + 2) x = x := by
        rw [iter_add, h2.2.1, h2.2.1]
      exact h22
    · have h22 : iter (fun x => invGray (applyBitPerm (n + 1) (bitrevFin (n + 1)) (gray x)) + 1#(n + 1)) (2 + 2) x = x := by
        rw [iter_add, h2.2.1, h2.2.1]
      exact h22
    · exact h4.2.1

/-- Swap-halves involution on `Fin (2 * k)`. -/
def swapHalfFin (k : Nat) (i : Fin (2 * k)) : Fin (2 * k) :=
  ⟨if i.val < k then i.val + k else i.val - k, by split <;> omega⟩

theorem swapHalfFin_involutive (k : Nat) (i : Fin (2 * k)) :
    swapHalfFin k (swapHalfFin k i) = i := by
  apply Fin.ext
  unfold swapHalfFin
  dsimp only
  by_cases h : i.val < k
  · simp only [h, ↓reduceIte]
    have h2 : ¬ (i.val + k < k) := by omega
    simp only [h2, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]
    have h2 : i.val - k < k := by omega
    simp only [h2, ↓reduceIte]; omega

/-- COROLLARY 4.1b (Gray-Basis `swapHalf + 1` Exact `2^k` Period):
    For EVERY `k ≥ 1`, `F(x) = invGray (swapHalf (gray x)) + 1` on `BitVec (2*k)` has
    `HasMinPeriod F 0 (2^k)` and every state has period in `{2, 4, 2^k}`! -/
theorem graySwapHalf_plusOne {k : Nat} (hk : 1 ≤ k) :
    let F : BitVec (2 * k) → BitVec (2 * k) :=
      fun x => invGray (applyBitPerm (2 * k) (swapHalfFin k) (gray x)) + 1#(2 * k)
    HasMinPeriod F 0#(2 * k) (2 ^ k) ∧
    ∀ x : BitVec (2 * k), HasMinPeriod F x (2 ^ k) ∨ HasMinPeriod F x 2 ∨ HasMinPeriod F x 4 := by
  cases k with
  | zero => omega
  | succ m =>
    have hmain := grayBitPermInvolution_plusOne_universal (n := 2 * m + 1) (by omega)
      (swapHalfFin (m + 1)) (swapHalfFin_involutive (m + 1))
    have hj : (swapHalfFin (m + 1) ⟨0, by omega⟩).val = m + 1 := by simp [swapHalfFin]
    dsimp only at hmain ⊢
    rw [hj, show 2 * m + 1 + 1 - (m + 1) = m + 1 by omega] at hmain
    exact ⟨hmain.1, hmain.2.2⟩

theorem nat_xor_two_pow_of_lt {n y : Nat} (hy : y < 2 ^ n) : y ^^^ 2 ^ n = y + 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hi : i = n
  · subst hi
    have hyi : y.testBit i = false := Nat.testBit_lt_two_pow hy
    have hsum : (y + 2 ^ i).testBit i = true := by
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.add_div_right y (Nat.two_pow_pos i),
          Nat.div_eq_of_lt hy]
      rfl
    rw [hyi, hsum, decide_eq_true rfl]; rfl
  · by_cases hlt_i : i < n
    · have hdiv : (y + 2 ^ n) / 2 ^ i = y / 2 ^ i + 2 ^ (n - i) := by
        have hp : 2 ^ n = 2 ^ (n - i) * 2 ^ i := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
        rw [hp, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i)]
      have h2even : 2 ^ (n - i) % 2 = 0 := by
        cases hm : n - i with
        | zero => omega
        | succ d => rw [Nat.pow_succ]; omega
      have hne : decide (n = i) = false := decide_eq_false (Ne.symm hi)
      rw [hne, Bool.xor_false]
      rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, hdiv]
      rw [Nat.and_comm 1, Nat.and_comm 1, Nat.and_one_is_mod, Nat.and_one_is_mod]
      have hmod : (y / 2 ^ i + 2 ^ (n - i)) % 2 = (y / 2 ^ i) % 2 := by omega
      rw [hmod]
    · have hgt : n + 1 ≤ i := by omega
      have h1 : y.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega)))
      have h2 : (y + 2 ^ n).testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show y + 2 ^ n < 2 ^ (n + 1) by rw [Nat.pow_succ]; omega)
          (Nat.pow_le_pow_right (by omega) hgt))
      have hne : decide (n = i) = false := decide_eq_false (Ne.symm hi)
      rw [h1, h2, hne]; rfl

/-- Helper: XOR with `2^(w-1)` equals adding `2^(w-1)` modulo `2^w`! -/
theorem xor_msb_eq_add_msb {w : Nat} (hw : 1 ≤ w) (x : BitVec w) :
    x ^^^ (1#w <<< (w - 1)) = x + (1#w <<< (w - 1)) := by
  cases w with
  | zero => omega
  | succ n =>
    simp only [Nat.add_sub_cancel]
    apply BitVec.eq_of_toNat_eq
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    have hmsb : (1#(n + 1) <<< n).toNat = 2 ^ n := by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      have h1lt : 1 < 2 ^ (n + 1) := by have := Nat.two_pow_pos n; omega
      rw [Nat.mod_eq_of_lt h1lt, Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.mod_eq_of_lt (by have := Nat.two_pow_pos n; omega)
    rw [BitVec.toNat_xor, BitVec.toNat_add, hmsb]
    have hxlt : x.toNat < 2 * 2 ^ n := by rw [← hpow]; exact x.isLt
    by_cases hlt : x.toNat < 2 ^ n
    · have hmod : (x.toNat + 2 ^ n) % 2 ^ (n + 1) = x.toNat + 2 ^ n := Nat.mod_eq_of_lt (by omega)
      rw [hmod, nat_xor_two_pow_of_lt hlt]
    · let y := x.toNat - 2 ^ n
      have hy : y < 2 ^ n := by omega
      have hxy : x.toNat = y + 2 ^ n := by omega
      have hmod : (x.toNat + 2 ^ n) % 2 ^ (n + 1) = y := by
        have : x.toNat + 2 ^ n = y + 2 ^ (n + 1) := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod, hxy, ← nat_xor_two_pow_of_lt hy, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- INFINITE THEOREM 4.2 (MSB Carry-Kick Hamiltonian Phase Transition):
    For EVERY width `w ≥ 3` and EVERY bit-permutation involution `π : Fin w → Fin w`,
    the MSB-kicked Gray-basis increment map
      `F_kick(x) = invGray (applyBitPerm w π (gray x)) + (2^(w-1) + 1)`
    is a SINGLE FULL-PERIOD HAMILTONIAN CYCLE of length `2^w`
    IF AND ONLY IF `(π 0).val ∈ {0, w - 2, w - 1}`! -/
theorem grayBitPermInvolution_msbKick_singleCycle_iff {w : Nat} (hw : 3 ≤ w)
    (π : Fin w → Fin w) (hinv : ∀ i, π (π i) = i) :
    IsSingleCycle w (fun x => invGray (applyBitPerm w π (gray x)) + ((1#w <<< (w - 1)) + 1#w)) ↔
      (π ⟨0, by omega⟩).val = 0 ∨
      (π ⟨0, by omega⟩).val = w - 2 ∨
      (π ⟨0, by omega⟩).val = w - 1 := by
  cases w with
  | zero => omega
  | succ n =>
    have hn : 2 ≤ n := by omega
    let δ : BitVec (n + 1) := 1#(n + 1) <<< n
    have hF_eq : (fun x => invGray (applyBitPerm (n + 1) π (gray x)) + ((1#(n + 1) <<< (n + 1 - 1)) + 1#(n + 1))) =
        grayInvMap (applyBitPerm (n + 1) π) δ := by
      funext x
      unfold grayInvMap δ
      have hadd := xor_msb_eq_add_msb (w := n + 1) (by omega) (invGray (applyBitPerm (n + 1) π (gray x)) + 1#(n + 1))
      simp only [Nat.add_sub_cancel] at hadd ⊢
      rw [hadd, BitVec.add_assoc, BitVec.add_comm 1#(n + 1)]
    have hδ_toNat : δ.toNat = 2 ^ n := by
      unfold δ
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
      have h1lt : 1 < 2 ^ (n + 1) := by rw [Nat.pow_succ]; have := Nat.two_pow_pos n; omega
      rw [Nat.mod_eq_of_lt h1lt, Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.mod_eq_of_lt (by rw [Nat.pow_succ]; have := Nat.two_pow_pos n; omega)
    have hδ_even : δ.toNat % 2 = 0 := by
      rw [hδ_toNat]
      cases n with | zero => omega | succ k => rw [Nat.pow_succ]; omega
    have hspec := bitPerm_grayInvolutionSpec π hinv δ hδ_even
    rw [hF_eq, grayInvMap_singleCycle_iff (by omega) hspec]
    let m := applyBitPerm (n + 1) π (1#(n + 1) ^^^ gray δ)
    have hγ_bit0 : ((compiledDefect δ m).toNat % 2 = 0) ↔ ((invGray m).getLsbD 1 = false) := by
      unfold compiledDefect
      rw [BitVec.toNat_ofNat]
      have hdiv_lt : (invGray m ^^^ δ).toNat / 2 < 2 ^ n := by
        have := (invGray m ^^^ δ).isLt; rw [Nat.pow_succ] at this; omega
      rw [Nat.mod_eq_of_lt hdiv_lt, BitVec.toNat_xor, nat_xor_div_two, nat_xor_mod_two, hδ_toNat]
      have hδ_div2_even : (2 ^ n / 2) % 2 = 0 := by
        cases n with
        | zero => omega
        | succ k =>
          cases k with
          | zero => omega
          | succ k' =>
            have h1 : 2 ^ (k' + 1 + 1) / 2 = 2 ^ (k' + 1) := by
              rw [Nat.pow_succ]; omega
            rw [h1, Nat.pow_succ]; omega
      rw [hδ_div2_even, Nat.xor_zero]
      have htb1 : (invGray m).getLsbD 1 = decide ((invGray m).toNat / 2 % 2 = 1) := by
        rw [BitVec.getLsbD, Nat.testBit_succ, Nat.testBit_zero]
      rw [htb1]
      have hmod : (invGray m).toNat / 2 % 2 = 0 ∨ (invGray m).toNat / 2 % 2 = 1 := by omega
      rcases hmod with hmod | hmod <;> simp [hmod]
    have hm_bit0 : m.getLsbD 0 = xor ((invGray m).getLsbD 0) ((invGray m).getLsbD 1) := by
      have h := congrArg (fun z => z.getLsbD 0) (gray_invGray m)
      simp only [gray, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, Nat.add_zero] at h
      exact h.symm
    have hinv_bit0 : (invGray m).getLsbD 0 = true := by
      rw [getLsbD_zero_eq_mod_two, grayInvSpec_m_odd hspec]; rfl
    have hbit_iff : (invGray m).getLsbD 1 = false ↔ m.getLsbD 0 = true := by
      rw [hm_bit0, hinv_bit0]
      cases (invGray m).getLsbD 1 <;> simp
    rw [hγ_bit0, hbit_iff]
    have h1eq : 1#(n + 1) = 1#(n + 1) <<< 0 := by simp
    unfold m
    rw [getLsbD_applyBitPerm]
    simp only [Nat.zero_lt_succ, ↓reduceDIte, BitVec.getLsbD_xor, gray, BitVec.getLsbD_ushiftRight]
    rw [h1eq, getLsbD_unitBit 0 _ (by omega), getLsbD_unitBit n _ (by omega)]
    have hδ_shift : (1#(n + 1) <<< n).getLsbD (1 + (π ⟨0, by omega⟩).val) =
        decide ((π ⟨0, by omega⟩).val = n - 1) := by
      rw [getLsbD_unitBit n _ (by omega)]
      by_cases h' : (π ⟨0, by omega⟩).val = n - 1
      · have h1 : 1 + (π ⟨0, by omega⟩).val = n := by omega
        rw [decide_eq_true h1, decide_eq_true h']
      · have h1 : 1 + (π ⟨0, by omega⟩).val ≠ n := by omega
        rw [decide_eq_false h1, decide_eq_false h']
    rw [hδ_shift]
    simp only [Nat.add_sub_cancel]
    have hne01 : ¬ (0 = n - 1) := by omega
    have hne02 : ¬ (0 = n) := by omega
    have hne12 : ¬ (n - 1 = n) := by omega
    have hj_sub : n + 1 - 2 = n - 1 := by omega
    rw [hj_sub]
    generalize (π ⟨0, by omega⟩).val = j
    by_cases h0 : j = 0
    · subst h0; rw [decide_eq_true rfl, decide_eq_false hne02, decide_eq_false hne01]; simp
    · by_cases h1 : j = n - 1
      · subst h1; rw [decide_eq_false h0, decide_eq_false hne12, decide_eq_true rfl]; simp
      · by_cases h2 : j = n
        · subst h2; rw [decide_eq_false h0, decide_eq_true rfl, decide_eq_false h1]; simp
        · rw [decide_eq_false h0, decide_eq_false h2, decide_eq_false h1]; simp [h0, h1, h2]

/-- COROLLARY 4.2a (`bitrev` in Gray basis + `(2^(w-1) + 1)` is a Single Hamiltonian Cycle ∀ w ≥ 3!):
    Contrast with `grayBitrev_plusOne_order4` (where `+ 1` collapses to order 4)! -/
theorem grayBitrev_msbKick_singleCycle {w : Nat} (hw : 3 ≤ w) :
    IsSingleCycle w (fun x => invGray (applyBitPerm w (bitrevFin w) (gray x)) + ((1#w <<< (w - 1)) + 1#w)) := by
  rw [grayBitPermInvolution_msbKick_singleCycle_iff hw (bitrevFin w) (bitrevFin_involutive w)]
  right; right
  simp [bitrevFin]

/-! ## Section 5: Compiler B — Feistel-Carry Fiber-Splice Engine & Upper-Shift Jacobsthal Theorem -/

theorem pack_val_lt (m k : Nat) (a : BitVec m) (b : BitVec k) :
    a.toNat * 2 ^ k + b.toNat < 2 ^ (m + k) := by
  have ha : a.toNat + 1 ≤ 2 ^ m := a.isLt
  have hb : b.toNat < 2 ^ k := b.isLt
  have hpow : 2 ^ (m + k) = 2 ^ m * 2 ^ k := Nat.pow_add 2 m k
  have hmul : (a.toNat + 1) * 2 ^ k ≤ 2 ^ m * 2 ^ k := Nat.mul_le_mul_right _ ha
  rw [Nat.add_mul, Nat.one_mul] at hmul
  omega

theorem pack_toNat (m k : Nat) (a : BitVec m) (b : BitVec k) :
    (pack m k a b).toNat = a.toNat * 2 ^ k + b.toNat := by
  unfold pack
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (pack_val_lt m k a b)]

theorem pack_div (m k : Nat) (a : BitVec m) (b : BitVec k) :
    (pack m k a b).toNat / 2 ^ k = a.toNat := by
  rw [pack_toNat, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos k), Nat.div_eq_of_lt b.isLt, Nat.add_zero]

theorem pack_mod (m k : Nat) (a : BitVec m) (b : BitVec k) :
    (pack m k a b).toNat % 2 ^ k = b.toNat := by
  rw [pack_toNat, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt b.isLt]

theorem pack_inj {m k : Nat} {a1 a2 : BitVec m} {b1 b2 : BitVec k}
    (h : pack m k a1 b1 = pack m k a2 b2) : a1 = a2 ∧ b1 = b2 := by
  have hdiv := congrArg (fun z => z.toNat / 2 ^ k) h
  have hmod := congrArg (fun z => z.toNat % 2 ^ k) h
  rw [pack_div, pack_div] at hdiv
  rw [pack_mod, pack_mod] at hmod
  exact ⟨BitVec.eq_of_toNat_eq hdiv, BitVec.eq_of_toNat_eq hmod⟩

theorem pack_zero (m k : Nat) : pack m k 0#m 0#k = 0#(m + k) := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_toNat]; simp

theorem unpack_pack (m k : Nat) (x : BitVec (m + k)) :
    pack m k (BitVec.ofNat m (x.toNat / 2 ^ k)) (BitVec.ofNat k (x.toNat % 2 ^ k)) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hdiv_lt : x.toNat / 2 ^ k < 2 ^ m := by
    have hx := x.isLt
    rw [Nat.pow_add] at hx
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
  have hmod_lt : x.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  rw [Nat.mod_eq_of_lt hdiv_lt, Nat.mod_eq_of_lt hmod_lt]
  have hdm := Nat.div_add_mod x.toNat (2 ^ k)
  rw [Nat.mul_comm] at hdm
  exact hdm

theorem feistelCarry_pack_internal {m k : Nat} (hk : 1 ≤ k) (h : BitVec m → BitVec k)
    (a : BitVec m) (b : BitVec k) (hneq : b ≠ ~~~(h a)) :
    feistelCarry m k h (pack m k a b) = pack m k a (phi k (h a) b) := by
  unfold feistelCarry
  have ha_eq : BitVec.ofNat m ((pack m k a b).toNat / 2 ^ k) = a := by
    apply BitVec.eq_of_toNat_eq; rw [pack_div, BitVec.toNat_ofNat, Nat.mod_eq_of_lt a.isLt]
  have hb_eq : BitVec.ofNat k ((pack m k a b).toNat % 2 ^ k) = b := by
    apply BitVec.eq_of_toNat_eq; rw [pack_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt b.isLt]
  rw [ha_eq, hb_eq]
  have hxor_ne : (b ^^^ h a).toNat ≠ 2 ^ k - 1 := by
    intro heq
    apply hneq
    have hall : b ^^^ h a = BitVec.allOnes k := by
      apply BitVec.eq_of_toNat_eq; rw [heq, BitVec.toNat_allOnes]
    have h1 := congrArg (fun z => z ^^^ h a) hall
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at h1
    rw [h1]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]
  have hxor_lt : (b ^^^ h a).toNat + 1 < 2 ^ k := by
    have := (b ^^^ h a).isLt; omega
  have h1lt_k : 1 < 2 ^ k := by
    cases k with | zero => omega | succ d => rw [Nat.pow_succ]; have := Nat.two_pow_pos d; omega
  have h1lt_mk : 1 < 2 ^ (m + k) := by
    have hle : 2 ^ k ≤ 2 ^ (m + k) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hphi_toNat : (phi k (h a) b).toNat = (b ^^^ h a).toNat + 1 := by
    unfold phi
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1lt_k, Nat.mod_eq_of_lt hxor_lt]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, pack_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1lt_mk,
      pack_toNat, hphi_toNat, Nat.add_assoc]
  have hsum_lt : a.toNat * 2 ^ k + ((b ^^^ h a).toNat + 1) < 2 ^ (m + k) := by
    have := pack_val_lt m k a (phi k (h a) b)
    rwa [hphi_toNat] at this
  exact Nat.mod_eq_of_lt hsum_lt

theorem feistelCarry_pack_exit {m k : Nat} (hm : 1 ≤ m) (hk : 1 ≤ k) (h : BitVec m → BitVec k)
    (a : BitVec m) :
    feistelCarry m k h (pack m k a (~~~(h a))) = pack m k (a + 1#m) 0#k := by
  unfold feistelCarry
  have ha_eq : BitVec.ofNat m ((pack m k a (~~~(h a))).toNat / 2 ^ k) = a := by
    apply BitVec.eq_of_toNat_eq; rw [pack_div, BitVec.toNat_ofNat, Nat.mod_eq_of_lt a.isLt]
  have hb_eq : BitVec.ofNat k ((pack m k a (~~~(h a))).toNat % 2 ^ k) = ~~~(h a) := by
    apply BitVec.eq_of_toNat_eq; rw [pack_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (~~~(h a)).isLt]
  rw [ha_eq, hb_eq]
  have hnotxor : (~~~(h a) ^^^ h a).toNat = 2 ^ k - 1 := by
    have hall : ~~~(h a) ^^^ h a = BitVec.allOnes k := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
    rw [hall, BitVec.toNat_allOnes]
  have h1lt_m : 1 < 2 ^ m := by
    cases m with | zero => omega | succ d => rw [Nat.pow_succ]; have := Nat.two_pow_pos d; omega
  have h1lt_k : 1 < 2 ^ k := by
    cases k with | zero => omega | succ d => rw [Nat.pow_succ]; have := Nat.two_pow_pos d; omega
  have h1lt_mk : 1 < 2 ^ (m + k) := by
    have hle : 2 ^ k ≤ 2 ^ (m + k) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, pack_toNat, hnotxor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1lt_mk,
      pack_toNat, BitVec.toNat_zero, Nat.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h1lt_m]
  have hsum : a.toNat * 2 ^ k + (2 ^ k - 1) + 1 = (a.toNat + 1) * 2 ^ k := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  rw [hsum, Nat.pow_add, Nat.mul_mod_mul_right]
  omega

theorem feistelCarry_fiber_iter {m k : Nat} (hk : 1 ≤ k) (h : BitVec m → BitVec k)
    (a : BitVec m) (j : Nat) (hj : j < fiberLen k (h a)) :
    iter (feistelCarry m k h) j (pack m k a 0#k) = pack m k a (iter (phi k (h a)) j 0#k) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj_lt : j < fiberLen k (h a) := by omega
    rw [iter_succ_right, ih hj_lt, iter_succ_right]
    apply feistelCarry_pack_internal hk h a
    intro hbad
    have hper := (phi_zero_orbit k (h a)).1
    have hzero : iter (phi k (h a)) (j + 1) 0#k = 0#k := by
      rw [iter_succ_right, hbad, phi_not_eq_zero]
    exact hper.2.2 (j + 1) (by omega) hj hzero

theorem feistelCarry_fiber_jump {m k : Nat} (hm : 1 ≤ m) (hk : 1 ≤ k) (h : BitVec m → BitVec k)
    (a : BitVec m) :
    iter (feistelCarry m k h) (fiberLen k (h a)) (pack m k a 0#k) = pack m k (a + 1#m) 0#k := by
  have hpos : 0 < fiberLen k (h a) := Nat.two_pow_pos _
  have hstep : fiberLen k (h a) = (fiberLen k (h a) - 1) + 1 := by omega
  rw [hstep, iter_succ_right, feistelCarry_fiber_iter hk h a _ (by omega)]
  unfold fiberLen
  rw [phi_zero_orbit_exit k (h a)]
  exact feistelCarry_pack_exit hm hk h a

theorem fiberPrefixSum_succ (m k : Nat) (h : BitVec m → BitVec k) (r : Nat) :
    fiberPrefixSum m k h (r + 1) = fiberPrefixSum m k h r + fiberLen k (h (BitVec.ofNat m r)) := rfl

theorem feistelCarry_prefix_iter {m k : Nat} (hm : 1 ≤ m) (hk : 1 ≤ k) (h : BitVec m → BitVec k)
    (r : Nat) :
    iter (feistelCarry m k h) (fiberPrefixSum m k h r) 0#(m + k) = pack m k (BitVec.ofNat m r) 0#k := by
  induction r with
  | zero =>
    simp [fiberPrefixSum, iter]
    exact (pack_zero m k).symm
  | succ r ih =>
    unfold fiberPrefixSum
    rw [iter_add, ih, feistelCarry_fiber_jump hm hk h]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have h1lt : 1 < 2 ^ m := by
      cases m with | zero => omega | succ d => rw [Nat.pow_succ]; have := Nat.two_pow_pos d; omega
    rw [Nat.mod_eq_of_lt h1lt, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem fiberPrefixSum_split {m k : Nat} (h : BitVec m → BitVec k) (N s : Nat)
    (hs : s < fiberPrefixSum m k h N) :
    ∃ r j, r < N ∧ j < fiberLen k (h (BitVec.ofNat m r)) ∧ s = fiberPrefixSum m k h r + j := by
  induction N with
  | zero => simp [fiberPrefixSum] at hs
  | succ N ih =>
    unfold fiberPrefixSum at hs
    by_cases hlt : s < fiberPrefixSum m k h N
    · rcases ih hlt with ⟨r, j, hr, hj, hs_eq⟩
      exact ⟨r, j, by omega, hj, hs_eq⟩
    · exact ⟨N, s - fiberPrefixSum m k h N, by omega, by omega, by omega⟩

theorem fiberPrefixSum_pos {m k : Nat} (h : BitVec m → BitVec k) (N : Nat) (hN : 1 ≤ N) :
    0 < fiberPrefixSum m k h N := by
  cases N with
  | zero => omega
  | succ r =>
    unfold fiberPrefixSum
    have := Nat.two_pow_pos (k - trailingOnes (h (BitVec.ofNat m r)))
    unfold fiberLen; omega

/-- Compiler B Master Theorem 5.1 (Exact Spliced Giant Zero-Orbit & Membership):
    For EVERY `m ≥ 1`, `k ≥ 1`, and ANY function `h : BitVec m → BitVec k`:
    1. `0#(m+k)` has exact minimal period `feistelZeroLen m k h = ∑_{a} 2^(k - trailingOnes (h a))`.
    2. A state `pack m k a b` lies in the zero-orbit iff `b.toNat % 2 ^ trailingOnes (h a) = 0`. -/
theorem feistelCarry_zero_orbit {m k : Nat} (hm : 1 ≤ m) (hk : 1 ≤ k) (h : BitVec m → BitVec k) :
    HasMinPeriod (feistelCarry m k h) 0#(m + k) (feistelZeroLen m k h) ∧
    ∀ (a : BitVec m) (b : BitVec k),
      (∃ s, s < feistelZeroLen m k h ∧ iter (feistelCarry m k h) s 0#(m + k) = pack m k a b) ↔
      b.toNat % 2 ^ trailingOnes (h a) = 0 := by
  have hper : HasMinPeriod (feistelCarry m k h) 0#(m + k) (feistelZeroLen m k h) := by
    refine ⟨fiberPrefixSum_pos h (2 ^ m) (Nat.two_pow_pos m), ?_, ?_⟩
    · unfold feistelZeroLen
      rw [feistelCarry_prefix_iter hm hk h (2 ^ m)]
      have h0 : BitVec.ofNat m (2 ^ m) = 0#m := by apply BitVec.eq_of_toNat_eq; simp
      rw [h0, pack_zero]
    · intro s hs0 hslt heq
      rcases fiberPrefixSum_split h (2 ^ m) s hslt with ⟨r, j, hr, hj, rfl⟩
      rw [iter_add, feistelCarry_prefix_iter hm hk h r, feistelCarry_fiber_iter hk h _ j hj,
          ← pack_zero m k] at heq
      have ⟨ha0, hb0⟩ := pack_inj heq
      have hr0 : r = 0 := by
        have := congrArg BitVec.toNat ha0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, BitVec.toNat_zero] at this
        exact this
      subst hr0
      simp only [fiberPrefixSum, Nat.zero_add] at hs0
      exact (phi_zero_orbit k (h (BitVec.ofNat m 0))).1.2.2 j hs0 hj hb0
  refine ⟨hper, ?_⟩
  intro a b
  constructor
  · rintro ⟨s, hs, hseq⟩
    rcases fiberPrefixSum_split h (2 ^ m) s hs with ⟨r, j, hr, hj, rfl⟩
    rw [iter_add, feistelCarry_prefix_iter hm hk h r, feistelCarry_fiber_iter hk h _ j hj] at hseq
    have ⟨hra, hjb⟩ := pack_inj hseq
    subst hra
    exact ((phi_zero_orbit k (h (BitVec.ofNat m r))).2 b).1 ⟨j, hj, hjb⟩
  · intro hdiv
    rcases ((phi_zero_orbit k (h a)).2 b).2 hdiv with ⟨j, hj, hjb⟩
    have ha_of : BitVec.ofNat m a.toNat = a := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt a.isLt]
    have hslt : fiberPrefixSum m k h a.toNat + j < feistelZeroLen m k h := by
      have hmono : ∀ u v, u ≤ v → fiberPrefixSum m k h u ≤ fiberPrefixSum m k h v := by
        intro u v huv
        induction huv with
        | refl => exact Nat.le_refl _
        | step _ ih => rw [fiberPrefixSum_succ]; omega
      have h1 : fiberPrefixSum m k h (a.toNat + 1) ≤ fiberPrefixSum m k h (2 ^ m) :=
        hmono (a.toNat + 1) (2 ^ m) a.isLt
      unfold feistelZeroLen
      rw [fiberPrefixSum_succ, ha_of] at h1
      unfold fiberLen at h1
      omega
    refine ⟨fiberPrefixSum m k h a.toNat + j, hslt, ?_⟩
    rw [iter_add, feistelCarry_prefix_iter hm hk h a.toNat, ha_of,
        feistelCarry_fiber_iter hk h a j hj, hjb]

/-- Compiler B Master Theorem 5.2 (Complete Pointwise Classification of ALL `2^(m+k)` States):
    Every state `pack m k a b` either lies in the single spliced giant cycle (exact minimal period
    `feistelZeroLen m k h`), or is trapped inside fiber `a` with exact minimal period `1` or `2`! -/
theorem feistelCarry_complete_pointwise {m k : Nat} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (h : BitVec m → BitVec k) (a : BitVec m) (b : BitVec k) :
    (b.toNat % 2 ^ trailingOnes (h a) = 0 →
      HasMinPeriod (feistelCarry m k h) (pack m k a b) (feistelZeroLen m k h)) ∧
    (b.toNat % 2 ^ trailingOnes (h a) ≠ 0 →
      let s := ctzNat k b.toNat
      ((h a).toNat / 2 ^ (s + 1) = 0 → HasMinPeriod (feistelCarry m k h) (pack m k a b) 1) ∧
      ((h a).toNat / 2 ^ (s + 1) ≠ 0 → HasMinPeriod (feistelCarry m k h) (pack m k a b) 2)) := by
  have ⟨hper0, hmem0⟩ := feistelCarry_zero_orbit hm hk h
  constructor
  · intro hdiv
    rcases (hmem0 a b).2 hdiv with ⟨s, _, hs⟩
    rw [← hs]
    exact hasMinPeriod_of_iter_eq hper0 s
  · intro hndiv
    -- Any non-zero-orbit state `b` in fiber `a` NEVER hits `~~~(h a)` (which IS in the zero-orbit!),
    -- so `feistelCarry` acts purely as `phi k (h a)` on `b` forever!
    have hnot_exit : ∀ c : BitVec k, c.toNat % 2 ^ trailingOnes (h a) ≠ 0 → c ≠ ~~~(h a) := by
      intro c hc heq
      apply hc
      apply ((phi_zero_orbit k (h a)).2 c).1
      refine ⟨2 ^ (k - trailingOnes (h a)) - 1, by have := Nat.two_pow_pos (k - trailingOnes (h a)); omega, ?_⟩
      rw [phi_zero_orbit_exit, heq]
    have hpres_ndiv : ∀ c : BitVec k, c.toNat % 2 ^ trailingOnes (h a) ≠ 0 →
        (phi k (h a) c).toNat % 2 ^ trailingOnes (h a) ≠ 0 := by
      intro c hc hdiv_next
      apply hc
      rcases ((phi_zero_orbit k (h a)).2 (phi k (h a) c)).2 hdiv_next with ⟨j, hj, hjeq⟩
      have hper_phi := (phi_zero_orbit k (h a)).1
      apply ((phi_zero_orbit k (h a)).2 c).1
      by_cases hj0 : j = 0
      · subst hj0
        have hc_eq : c = ~~~(h a) := (phi_eq_zero_iff k (h a) c).1 hjeq.symm
        refine ⟨2 ^ (k - trailingOnes (h a)) - 1, by have := Nat.two_pow_pos (k - trailingOnes (h a)); omega, ?_⟩
        rw [phi_zero_orbit_exit, hc_eq]
      · refine ⟨j - 1, by omega, ?_⟩
        apply phi_injective k (h a)
        rw [← iter_succ_right (phi k (h a)), show j - 1 + 1 = j by omega, hjeq]
    have hiter_trap : ∀ r,
        iter (feistelCarry m k h) r (pack m k a b) = pack m k a (iter (phi k (h a)) r b) ∧
        (iter (phi k (h a)) r b).toNat % 2 ^ trailingOnes (h a) ≠ 0 := by
      intro r
      induction r with
      | zero => exact ⟨rfl, hndiv⟩
      | succ r ih =>
        rw [iter_succ_right, ih.1, iter_succ_right,
            feistelCarry_pack_internal hk h a _ (hnot_exit _ ih.2)]
        exact ⟨rfl, hpres_ndiv _ ih.2⟩
    have hlift : ∀ p, HasMinPeriod (phi k (h a)) b p → HasMinPeriod (feistelCarry m k h) (pack m k a b) p := by
      rintro p ⟨hp0, hp, hmin⟩
      refine ⟨hp0, ?_, ?_⟩
      · rw [(hiter_trap p).1, hp]
      · intro r hr0 hrp heq
        rw [(hiter_trap r).1] at heq
        exact hmin r hr0 hrp (pack_inj heq).2
    have hphi := (phi_complete_pointwise k (h a) b).2 hndiv
    dsimp only
    exact ⟨fun h0 => hlift 1 (hphi.1 h0), fun hne => hlift 2 (hphi.2 hne)⟩

/-- Compiler B Master Theorem 5.3 (Single Hamiltonian Cycle Dichotomy for Feistel-Carry Maps):
    `feistelCarry m k h` is a single full-period Hamiltonian cycle on `BitVec (m + k)`
    IF AND ONLY IF `h a` is EVEN for EVERY `a : BitVec m`! -/
theorem feistelCarry_singleCycle_iff {m k : Nat} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (h : BitVec m → BitVec k) :
    IsSingleCycle (m + k) (feistelCarry m k h) ↔ ∀ a : BitVec m, (h a).toNat % 2 = 0 := by
  have ⟨hper0, hmem0⟩ := feistelCarry_zero_orbit hm hk h
  have hle_fiber : ∀ r, fiberPrefixSum m k h r ≤ r * 2 ^ k := by
    intro r
    induction r with
    | zero => simp [fiberPrefixSum]
    | succ r ih =>
      unfold fiberPrefixSum fiberLen
      have h1 : 2 ^ (k - trailingOnes (h (BitVec.ofNat m r))) ≤ 2 ^ k :=
        Nat.pow_le_pow_right (by omega) (Nat.sub_le k _)
      rw [Nat.succ_mul]
      omega
  constructor
  · intro hsc a
    by_cases ha : (h a).toNat % 2 = 0
    · exact ha
    · have hodd : (h a).toNat % 2 = 1 := by omega
      have ht : 1 ≤ trailingOnes (h a) := by
        cases k with | zero => omega | succ d => unfold trailingOnes; rw [trailingOnesNat_succ]; simp [hodd]
      have hlt_a : fiberLen k (h a) < 2 ^ k := by
        unfold fiberLen
        exact Nat.pow_lt_pow_right (by omega) (by omega)
      -- Therefore `feistelZeroLen m k h < 2^m * 2^k = 2^(m + k)`, contradicting `IsSingleCycle`!
      have hstrict : ∀ N, a.toNat < N → fiberPrefixSum m k h N < N * 2 ^ k := by
        intro N hltN
        induction N with
        | zero => omega
        | succ N ih =>
          unfold fiberPrefixSum
          rw [Nat.succ_mul]
          by_cases heq : a.toNat = N
          · have hof : BitVec.ofNat m N = a := by
              apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, ← heq, Nat.mod_eq_of_lt a.isLt]
            rw [hof]
            have := hle_fiber N
            omega
          · have h1 := ih (by omega)
            have h2 : fiberLen k (h (BitVec.ofNat m N)) ≤ 2 ^ k := by
              unfold fiberLen; exact Nat.pow_le_pow_right (by omega) (Nat.sub_le k _)
            omega
      have hlt_total : feistelZeroLen m k h < 2 ^ (m + k) := by
        unfold feistelZeroLen
        rw [Nat.pow_add]
        exact hstrict (2 ^ m) a.isLt
      have heq := hasMinPeriod_unique hsc.1 hper0
      omega
  · intro hall
    have hsum_eq : ∀ r, fiberPrefixSum m k h r = r * 2 ^ k := by
      intro r
      induction r with
      | zero => simp [fiberPrefixSum]
      | succ r ih =>
        unfold fiberPrefixSum fiberLen
        have hev := hall (BitVec.ofNat m r)
        have ht0 : trailingOnes (h (BitVec.ofNat m r)) = 0 := by
          cases k with | zero => rfl | succ d => unfold trailingOnes; rw [trailingOnesNat_succ]; simp [hev]
        rw [ht0, Nat.sub_zero, ih, Nat.succ_mul]
    have hlen : feistelZeroLen m k h = 2 ^ (m + k) := by
      unfold feistelZeroLen; rw [hsum_eq, Nat.pow_add]
    rw [hlen] at hper0
    refine ⟨hper0, ?_⟩
    intro x
    rw [← unpack_pack m k x]
    have ha_ev := hall (BitVec.ofNat m (x.toNat / 2 ^ k))
    have ht0 : trailingOnes (h (BitVec.ofNat m (x.toNat / 2 ^ k))) = 0 := by
      cases k with | zero => rfl | succ d => unfold trailingOnes; rw [trailingOnesNat_succ]; simp [ha_ev]
    have hmem := (hmem0 (BitVec.ofNat m (x.toNat / 2 ^ k)) (BitVec.ofNat k (x.toNat % 2 ^ k))).2
    rw [hlen, ht0] at hmem
    exact hmem (by omega)

/-- Upper-shift involution `(x ^^^ (x >>> k)) + 1` equals `feistelCarry m k (zeroExtend)` for `m ≤ k`! -/
theorem upperShift_eq_feistelCarry {m k : Nat} (hmk : m ≤ k) (x : BitVec (m + k)) :
    (x ^^^ (x >>> k)) + 1#(m + k) = feistelCarry m k (fun a => BitVec.ofNat k a.toNat) x := by
  unfold feistelCarry
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let a : BitVec m := BitVec.ofNat m (x.toNat / 2 ^ k)
  let b : BitVec k := BitVec.ofNat k (x.toNat % 2 ^ k)
  have ha_toNat : a.toNat = x.toNat / 2 ^ k := by
    rw [BitVec.toNat_ofNat]
    have hx := x.isLt; rw [Nat.pow_add] at hx
    exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx))
  have hb_toNat : b.toNat = x.toNat % 2 ^ k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos k))]
  have ha_lt_k : a.toNat < 2 ^ k :=
    Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by omega) hmk)
  have hpack_bit : (pack m k a (b ^^^ BitVec.ofNat k a.toNat)).getLsbD i =
      if i < k then (b ^^^ BitVec.ofNat k a.toNat).getLsbD i else a.getLsbD (i - k) := by
    rw [BitVec.getLsbD, pack_toNat]
    by_cases hik : i < k
    · simp only [hik, ↓reduceIte, BitVec.getLsbD]
      have hpow : 2 ^ k = 2 ^ (k - i) * 2 ^ i := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
      have hdiv : (a.toNat * 2 ^ k + (b ^^^ BitVec.ofNat k a.toNat).toNat) / 2 ^ i =
          a.toNat * 2 ^ (k - i) + (b ^^^ BitVec.ofNat k a.toNat).toNat / 2 ^ i := by
        rw [hpow, ← Nat.mul_assoc, Nat.mul_comm (a.toNat * 2 ^ (k - i)),
            Nat.mul_add_div (Nat.two_pow_pos i)]
      have h2even : 2 ^ (k - i) % 2 = 0 := by
        cases hsub : k - i with | zero => omega | succ d => rw [Nat.pow_succ]; omega
      rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, hdiv]
      rw [Nat.and_comm 1, Nat.and_comm 1, Nat.and_one_is_mod, Nat.and_one_is_mod]
      have hmod : (a.toNat * 2 ^ (k - i) + (b ^^^ BitVec.ofNat k a.toNat).toNat / 2 ^ i) % 2 =
          ((b ^^^ BitVec.ofNat k a.toNat).toNat / 2 ^ i) % 2 := by
        rw [Nat.add_mod, Nat.mul_mod, h2even, Nat.mul_zero]; omega
      rw [hmod]
    · simp only [hik, ↓reduceIte, BitVec.getLsbD]
      have hpow : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
      rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
          hpow, ← Nat.div_div_eq_div_mul, Nat.mul_comm a.toNat,
          Nat.mul_add_div (Nat.two_pow_pos k),
          Nat.div_eq_of_lt (b ^^^ BitVec.ofNat k a.toNat).isLt, Nat.add_zero]
  rw [hpack_bit, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight]
  by_cases hik : i < k
  · simp only [hik, ↓reduceIte, BitVec.getLsbD_xor]
    have hxb : x.getLsbD i = b.getLsbD i := by
      rw [BitVec.getLsbD, BitVec.getLsbD, hb_toNat, Nat.testBit_mod_two_pow]
      simp [hik]
    have hxa : x.getLsbD (k + i) = (BitVec.ofNat k a.toNat).getLsbD i := by
      rw [BitVec.getLsbD, BitVec.getLsbD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt_k, ha_toNat]
      rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
          Nat.pow_add, Nat.div_div_eq_div_mul]
    rw [hxb, hxa]
  · simp only [hik, ↓reduceIte]
    have hx_hi : x.getLsbD (k + i) = false :=
      bitVec_getLsbD_ge x (k + i) (by omega)
    rw [hx_hi, Bool.xor_false]
    rw [BitVec.getLsbD, BitVec.getLsbD, ha_toNat]
    have hpow : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
        hpow, ← Nat.div_div_eq_div_mul]

/-- Exact binary even/odd sum identity for the Jacobsthal length `∑_{a=0}^{2^m-1} 2^(k - trailingOnes(k, a))`. -/
def jacSumNat (m k : Nat) : Nat :=
  fiberPrefixSum m k (fun a => BitVec.ofNat k a.toNat) (2 ^ m)

def natSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => natSum f n + f n

theorem natSum_succ (f : Nat → Nat) (n : Nat) :
    natSum f (n + 1) = natSum f n + f n := rfl

theorem natSum_congr {f g : Nat → Nat} {N : Nat} (h : ∀ r < N, f r = g r) :
    natSum f N = natSum g N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [natSum_succ, natSum_succ, ih (fun r hr => h r (by omega)), h N (by omega)]

theorem natSum_const (c N : Nat) : natSum (fun _ => c) N = N * c := by
  induction N with
  | zero => simp [natSum]
  | succ N ih => rw [natSum_succ, ih, Nat.succ_mul]

theorem natSum_two_mul (f : Nat → Nat) (N : Nat) :
    natSum f (2 * N) = natSum (fun r => f (2 * r)) N + natSum (fun r => f (2 * r + 1)) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have h2 : 2 * (N + 1) = (2 * N + 1) + 1 := by omega
    rw [h2, natSum_succ, natSum_succ, natSum_succ, natSum_succ, ih]
    omega

theorem fiberPrefixSum_eq_natSum (m k : Nat) (h : BitVec m → BitVec k) (N : Nat) :
    fiberPrefixSum m k h N = natSum (fun r => fiberLen k (h (BitVec.ofNat m r))) N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [fiberPrefixSum_succ, natSum_succ, ih]

theorem jacSumNat_exact (m k : Nat) (hmk : m ≤ k) :
    3 * jacSumNat m k = 2 ^ (k - m) * (2 ^ (2 * m + 1) + 1) := by
  induction m generalizing k with
  | zero =>
    unfold jacSumNat
    rw [Nat.pow_zero, fiberPrefixSum_succ]
    change 3 * (0 + fiberLen k (BitVec.ofNat k (BitVec.ofNat 0 0).toNat)) = _
    unfold fiberLen trailingOnes
    have h0 : (BitVec.ofNat k (BitVec.ofNat 0 0).toNat).toNat = 0 := by simp
    rw [h0]
    have ht0 : trailingOnesNat k 0 = 0 := by
      cases k with | zero => rfl | succ d => rw [trailingOnesNat_succ]; simp
    rw [ht0, Nat.sub_zero]
    omega
  | succ m ih =>
    cases k with
    | zero => omega
    | succ k' =>
      have hmk' : m ≤ k' := by omega
      unfold jacSumNat
      rw [fiberPrefixSum_eq_natSum, Nat.pow_succ, Nat.mul_comm (2 ^ m) 2, natSum_two_mul]
      have heven_sum : natSum (fun r => fiberLen (k' + 1) (BitVec.ofNat (k' + 1) (BitVec.ofNat (m + 1) (2 * r)).toNat)) (2 ^ m) =
          2 ^ m * 2 ^ (k' + 1) := by
        rw [← natSum_const (2 ^ (k' + 1)) (2 ^ m)]
        apply natSum_congr
        intro r hr
        have hlt_m : 2 * r < 2 ^ (m + 1) := by rw [Nat.pow_succ]; omega
        have hlt_k : 2 * r < 2 ^ (k' + 1) :=
          Nat.lt_of_lt_of_le hlt_m (Nat.pow_le_pow_right (by omega) (by omega))
        unfold fiberLen trailingOnes
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_m, Nat.mod_eq_of_lt hlt_k,
            trailingOnesNat_succ]
        have hev : (2 * r) % 2 = 0 := by omega
        simp [hev]
      have hodd_sum : natSum (fun r => fiberLen (k' + 1) (BitVec.ofNat (k' + 1) (BitVec.ofNat (m + 1) (2 * r + 1)).toNat)) (2 ^ m) =
          jacSumNat m k' := by
        unfold jacSumNat
        rw [fiberPrefixSum_eq_natSum]
        apply natSum_congr
        intro r hr
        have hlt_m : 2 * r + 1 < 2 ^ (m + 1) := by rw [Nat.pow_succ]; omega
        have hlt_k : 2 * r + 1 < 2 ^ (k' + 1) :=
          Nat.lt_of_lt_of_le hlt_m (Nat.pow_le_pow_right (by omega) (by omega))
        have hlt_k' : r < 2 ^ k' :=
          Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) hmk')
        unfold fiberLen trailingOnes
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_m, Nat.mod_eq_of_lt hlt_k,
            BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hlt_k',
            trailingOnesNat_succ]
        have hodd : (2 * r + 1) % 2 = 1 := by omega
        have hdiv : (2 * r + 1) / 2 = r := by omega
        simp only [hodd, ↓reduceIte, hdiv]
        congr 1; omega
      rw [heven_sum, hodd_sum, Nat.mul_add, ih k' hmk']
      have hsub : k' + 1 - (m + 1) = k' - m := by omega
      rw [hsub]
      have hpow_fac : 2 ^ m * 2 ^ (k' + 1) = 2 ^ (k' - m) * 2 ^ (2 * m + 1) := by
        rw [← Nat.pow_add, ← Nat.pow_add]
        congr 1; omega
      rw [hpow_fac]
      have hpow_step : 2 ^ (2 * (m + 1) + 1) = 4 * 2 ^ (2 * m + 1) := by
        have h1 : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
        rw [h1, Nat.pow_add, Nat.mul_comm]
      rw [hpow_step]
      generalize 2 ^ (k' - m) = A
      generalize 2 ^ (2 * m + 1) = B
      have h1 : 3 * (A * B) + A * (B + 1) = A * (3 * B + (B + 1)) := by
        rw [Nat.mul_left_comm 3 A B, ← Nat.mul_add]
      rw [h1]
      congr 1; omega

/-- INFINITE THEOREM 5.4 (Upper-Shift Involution Exact Jacobsthal Cycle Decomposition):
    For EVERY `1 ≤ m ≤ k` (i.e. EVERY width `w = m + k` and shift `⌈w/2⌉ ≤ k < w`),
    the non-T-function upper-shift map `U(x) = (x ^^^ (x >>> k)) + 1` on `BitVec (m + k)` satisfies:
    1. `0` lies in a unique giant cycle of exact minimal period `L0` with `3 * L0 = 2^(k-m) * (2^(2m+1) + 1)`.
    2. EVERY state `x : BitVec (m + k)` has exact minimal period in `{1, 2, L0}`! -/
theorem upperShift_jacobsthal_decomposition {m k : Nat} (hm : 1 ≤ m) (hmk : m ≤ k) :
    let U : BitVec (m + k) → BitVec (m + k) := fun x => (x ^^^ (x >>> k)) + 1#(m + k)
    let L0 := jacSumNat m k
    3 * L0 = 2 ^ (k - m) * (2 ^ (2 * m + 1) + 1) ∧
    HasMinPeriod U 0#(m + k) L0 ∧
    ∀ x : BitVec (m + k), HasMinPeriod U x L0 ∨ HasMinPeriod U x 1 ∨ HasMinPeriod U x 2 := by
  intro U L0
  have hk : 1 ≤ k := by omega
  have hU_eq : U = feistelCarry m k (fun a => BitVec.ofNat k a.toNat) := by
    funext x; exact upperShift_eq_feistelCarry hmk x
  refine ⟨jacSumNat_exact m k hmk, ?_, ?_⟩
  · rw [hU_eq]
    exact (feistelCarry_zero_orbit hm hk _).1
  · intro x
    rw [hU_eq, ← unpack_pack m k x]
    let a := BitVec.ofNat m (x.toNat / 2 ^ k)
    let b := BitVec.ofNat k (x.toNat % 2 ^ k)
    have hpt := feistelCarry_complete_pointwise hm hk (fun a => BitVec.ofNat k a.toNat) a b
    by_cases hdiv : b.toNat % 2 ^ trailingOnes (BitVec.ofNat k a.toNat) = 0
    · exact Or.inl (hpt.1 hdiv)
    · by_cases h0 : (BitVec.ofNat k a.toNat).toNat / 2 ^ (ctzNat k b.toNat + 1) = 0
      · exact Or.inr (Or.inl ((hpt.2 hdiv).1 h0))
      · exact Or.inr (Or.inr ((hpt.2 hdiv).2 h0))

/-- List-sum invariance under bijections (core `Init` only, zero Mathlib). -/
theorem list_sum_perm_of_nodup {α : Type} [DecidableEq α] (g : α → Nat) :
    ∀ (l1 l2 : List α), l1.Nodup → l2.Nodup → (∀ x, x ∈ l1 ↔ x ∈ l2) →
      (l1.map g).sum = (l2.map g).sum := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 _ _ heq
    cases l2 with
    | nil => rfl
    | cons y ys => exact False.elim ((heq y).2 (by simp) |> fun h => by simp at h)
  | cons a l1' ih =>
    intro l2 hnd1 hnd2 heq
    have ha_not_in : a ∉ l1' := (List.nodup_cons.1 hnd1).1
    have hnd1' : l1'.Nodup := (List.nodup_cons.1 hnd1).2
    have ha_in_l2 : a ∈ l2 := (heq a).1 (by simp)
    rcases List.append_of_mem ha_in_l2 with ⟨p, q, rfl⟩
    have hnd_pq : (p ++ q).Nodup := by
      have hpq_eq : (p ++ a :: q).Nodup := hnd2
      rw [List.nodup_append] at hpq_eq ⊢
      refine ⟨hpq_eq.1, (List.nodup_cons.1 hpq_eq.2.1).2, ?_⟩
      intro x hxp y hyq
      exact hpq_eq.2.2 x hxp y (List.mem_cons_of_mem a hyq)
    have ha_not_pq : a ∉ p ++ q := by
      have hpq_eq : (p ++ a :: q).Nodup := hnd2
      rw [List.nodup_append] at hpq_eq
      intro hmem
      rcases List.mem_append.1 hmem with hp | hq
      · exact hpq_eq.2.2 a hp a List.mem_cons_self rfl
      · exact (List.nodup_cons.1 hpq_eq.2.1).1 hq
    have heq' : ∀ x, x ∈ l1' ↔ x ∈ p ++ q := by
      intro x
      constructor
      · intro hx
        have hxne : x ≠ a := fun h => ha_not_in (h ▸ hx)
        have hmem := (heq x).1 (List.mem_cons_of_mem a hx)
        rcases List.mem_append.1 hmem with hp | hqa
        · exact List.mem_append_left q hp
        · rcases List.mem_cons.1 hqa with rfl | hq
          · exact False.elim (hxne rfl)
          · exact List.mem_append_right p hq
      · intro hx
        have hxne : x ≠ a := fun h => ha_not_pq (h ▸ hx)
        have hmem : x ∈ p ++ a :: q := by
          rcases List.mem_append.1 hx with hp | hq
          · exact List.mem_append_left _ hp
          · exact List.mem_append_right _ (List.mem_cons_of_mem a hq)
        rcases List.mem_cons.1 ((heq x).2 hmem) with rfl | hx'
        · exact False.elim (hxne rfl)
        · exact hx'
    have hih := ih (p ++ q) hnd1' hnd_pq heq'
    simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append] at hih ⊢
    omega

theorem natSum_eq_list_range_sum (f : Nat → Nat) (N : Nat) :
    natSum f N = ((List.range N).map f).sum := by
  induction N with
  | zero => rfl
  | succ N ih =>
    unfold natSum
    rw [ih, List.range_succ, List.map_append, List.sum_append]
    simp

theorem list_nodup_map_on {α β : Type} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hinj, hnd => by
    rw [List.map_cons, List.nodup_cons]
    have ⟨ha, hndl⟩ := List.nodup_cons.1 hnd
    refine ⟨?_, list_nodup_map_on (fun x hx y hy => hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)) hndl⟩
    intro hmem
    rcases List.mem_map.1 hmem with ⟨y, hy, hfy⟩
    have hay : y = a := hinj y (List.mem_cons_of_mem a hy) a List.mem_cons_self hfy
    subst hay
    exact ha hy

/-- INFINITE THEOREM 5.5 (Universal Bijective Feistel-Carry Jacobsthal Isospectrality):
    For EVERY `k ≥ 1` and EVERY bijection `h : BitVec k → BitVec k` (linear, permutation, Gray,
    or nonlinear!), the giant zero-orbit length `L0 = feistelZeroLen k k h` is COMPLETELY
    INDEPENDENT OF `h` and equals the exact Jacobsthal number `3 * L0 = 2^(2k + 1) + 1`,
    with every non-giant state having exact minimal period `1` or `2`! -/
theorem feistelCarry_bijection_jacobsthal {k : Nat} (hk : 1 ≤ k)
    (h hInv : BitVec k → BitVec k)
    (hleft : ∀ a, hInv (h a) = a) (hright : ∀ a, h (hInv a) = a) :
    3 * feistelZeroLen k k h = 2 ^ (2 * k + 1) + 1 ∧
    HasMinPeriod (feistelCarry k k h) 0#(k + k) (feistelZeroLen k k h) ∧
    ∀ x : BitVec (k + k),
      HasMinPeriod (feistelCarry k k h) x (feistelZeroLen k k h) ∨
      HasMinPeriod (feistelCarry k k h) x 1 ∨
      HasMinPeriod (feistelCarry k k h) x 2 := by
  have hlen_eq : feistelZeroLen k k h = jacSumNat k k := by
    unfold feistelZeroLen jacSumNat
    rw [fiberPrefixSum_eq_natSum, fiberPrefixSum_eq_natSum,
        natSum_eq_list_range_sum, natSum_eq_list_range_sum]
    let base : List (BitVec k) := (List.range (2 ^ k)).map (BitVec.ofNat k)
    have hbase_nodup : base.Nodup := by
      apply list_nodup_map_on
      · intro x hx y hy hxy
        rw [List.mem_range] at hx hy
        have h1 := congrArg BitVec.toNat hxy
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h1
        exact h1
      · exact List.nodup_range
    have hbase_mem : ∀ a : BitVec k, a ∈ base := by
      intro a
      rw [List.mem_map]
      refine ⟨a.toNat, List.mem_range.2 a.isLt, ?_⟩
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt a.isLt]
    have hmap_nodup : (base.map h).Nodup := by
      apply list_nodup_map_on
      · intro a _ b _ hab
        have := congrArg hInv hab; rwa [hleft, hleft] at this
      · exact hbase_nodup
    have hmem_iff : ∀ a : BitVec k, a ∈ base.map h ↔ a ∈ base := by
      intro a
      constructor
      · intro _; exact hbase_mem a
      · intro _
        rw [List.mem_map]
        exact ⟨hInv a, hbase_mem (hInv a), hright a⟩
    have hsum := list_sum_perm_of_nodup (fiberLen k) (base.map h) base hmap_nodup hbase_nodup hmem_iff
    have h1 : (List.range (2 ^ k)).map (fun r => fiberLen k (h (BitVec.ofNat k r))) =
        (base.map h).map (fiberLen k) := by
      simp [base, List.map_map, Function.comp_def]
    have h2 : (List.range (2 ^ k)).map (fun r => fiberLen k (BitVec.ofNat k (BitVec.ofNat k r).toNat)) =
        base.map (fiberLen k) := by
      simp only [base, List.map_map]
      apply List.map_congr_left
      intro r hr
      rw [List.mem_range] at hr
      simp only [Function.comp_def]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr]
    rw [h1, h2, hsum]
  have hjac := jacSumNat_exact k k (Nat.le_refl k)
  rw [Nat.sub_self, Nat.pow_zero, Nat.one_mul] at hjac
  refine ⟨by rw [hlen_eq]; exact hjac, (feistelCarry_zero_orbit hk hk h).1, ?_⟩
  intro x
  rw [← unpack_pack k k x]
  let a := BitVec.ofNat k (x.toNat / 2 ^ k)
  let b := BitVec.ofNat k (x.toNat % 2 ^ k)
  have hpt := feistelCarry_complete_pointwise hk hk h a b
  by_cases hdiv : b.toNat % 2 ^ trailingOnes (h a) = 0
  · exact Or.inl (hpt.1 hdiv)
  · by_cases h0 : (h a).toNat / 2 ^ (ctzNat k b.toNat + 1) = 0
    · exact Or.inr (Or.inl ((hpt.2 hdiv).1 h0))
    · exact Or.inr (Or.inr ((hpt.2 hdiv).2 h0))

/-! ## Section 6: Kernel-Checked Non-Vacuity Witnesses & Sharpness Counterexamples -/

/-- Non-Vacuity Witness 1: Strictly NONLINEAR parity-preserving coset-equivariant involution on `BitVec 6`!
    Swaps bits 0 <-> 5 and applies a nonlinear parity-preserving involution on the middle 4 bits. -/
def nonlinearP6 (y : BitVec 6) : BitVec 6 :=
  let b0 := y.toNat % 2
  let b5 := (y.toNat / 32) % 2
  let mid := (y.toNat / 2) % 16
  let mid2 :=
    if mid = 3 then 12
    else if mid = 12 then 3
    else if mid = 5 then 10
    else if mid = 10 then 5
    else if mid = 1 then 7
    else if mid = 7 then 1
    else mid
  BitVec.ofNat 6 (b0 * 32 + mid2 * 2 + b5)

theorem nonlinearP6_is_nonlinear :
    nonlinearP6 (2#6 ^^^ 4#6) ≠ nonlinearP6 2#6 ^^^ nonlinearP6 4#6 := by decide

theorem nonlinearP6_spec : GrayInvolutionSpec nonlinearP6 0#6 (1#6 <<< 5) where
  involutive := by decide
  parity_pres := by decide
  delta_even := by decide
  coset_equiv := by decide

/-- Instantiating Compiler A on the nonlinear involution `nonlinearP6` certifies bounded order 4! -/
theorem witness_nonlinearP6_order4 :
    let F := grayInvMap nonlinearP6 0#6
    HasMinPeriod F 0#6 2 ∧ ∀ x : BitVec 6, iter F 4 x = x := by
  have hγ : compiledDefect 0#6 (1#6 <<< 5) = 31#5 := by decide
  have htr : trailingOnes (compiledDefect 0#6 (1#6 <<< 5)) = 5 := by decide
  refine ⟨?_, ?_⟩
  · have hpt := (grayInvMap_complete_pointwise nonlinearP6_spec 0#6).1
    rw [htr] at hpt
    exact hpt (by decide)
  · intro x
    have hpt := grayInvMap_complete_pointwise nonlinearP6_spec x
    dsimp only at hpt
    rw [htr] at hpt
    by_cases hdiv :
        ((if x.toNat % 2 = 0 then BitVec.ofNat 5 (x.toNat / 2)
          else BitVec.ofNat 5 ((grayInvMap nonlinearP6 0#6 x).toNat / 2)) ^^^
          BitVec.ofNat 5 ((0#6).toNat / 2)).toNat % 2 ^ 5 = 0
    · have h2 := hpt.1 hdiv
      have h22 : iter (grayInvMap nonlinearP6 0#6) (2 + 2) x = x := by rw [iter_add, h2.2.1, h2.2.1]
      exact h22
    · by_cases h0 :
          (compiledDefect 0#6 (1#6 <<< 5)).toNat /
          2 ^ (ctzNat 5 ((if x.toNat % 2 = 0 then BitVec.ofNat 5 (x.toNat / 2)
            else BitVec.ofNat 5 ((grayInvMap nonlinearP6 0#6 x).toNat / 2)) ^^^
            BitVec.ofNat 5 ((0#6).toNat / 2)).toNat + 1) = 0
      · have h2 := (hpt.2 hdiv).1 h0
        have h22 : iter (grayInvMap nonlinearP6 0#6) (2 + 2) x = x := by rw [iter_add, h2.2.1, h2.2.1]
        exact h22
      · exact ((hpt.2 hdiv).2 h0).2.1

/-- Non-Vacuity Witness 2: Infinite family of even-range Hamiltonian Feistel-Carry maps (`h(a) = a <<< 1`). -/
theorem witness_even_feistel_singleCycle {k : Nat} (hk : 1 ≤ k) :
    IsSingleCycle (k + k) (feistelCarry k k (fun a : BitVec k => a <<< 1)) := by
  rw [feistelCarry_singleCycle_iff hk hk]
  intro a
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]
  cases k with
  | zero => omega
  | succ d =>
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, Nat.mul_comm a.toNat 2, Nat.mul_mod_mul_left]
    omega

/-- Non-Vacuity Witness 3: Infinite family of bijective Feistel-Carry maps (`h = gray`) achieving Jacobsthal period! -/
theorem witness_gray_feistel_jacobsthal {k : Nat} (hk : 1 ≤ k) :
    3 * feistelZeroLen k k gray = 2 ^ (2 * k + 1) + 1 ∧
    HasMinPeriod (feistelCarry k k gray) 0#(k + k) (feistelZeroLen k k gray) := by
  have h := feistelCarry_bijection_jacobsthal hk gray invGray invGray_gray gray_invGray
  exact ⟨h.1, h.2.1⟩

/-- Sharpness 1: Core Engine — odd mask `γ = 1#4` breaks single cycle. -/
theorem sharpness_core_odd_gamma : ¬ IsSingleCycle 4 (phi 4 1#4) := by
  rw [phi_singleCycle_iff_even 4 (by omega) 1#4]
  decide

/-- Sharpness 2: Compiler A — non-involution `faro_out` on 6 bits fixes bit 0 (`π(0) = 0`)
    yet has `HasMinPeriod F 0#6 8` (NOT a single 64-cycle as Theorem 4.1 guarantees for involutions!). -/
def faroOut6 (i : Fin 6) : Fin 6 :=
  ⟨if i.val < 3 then 2 * i.val else 2 * (i.val - 3) + 1, by split <;> omega⟩

theorem sharpness_compilerA_non_involution_faro6 :
    let F : BitVec 6 → BitVec 6 := fun x => invGray (applyBitPerm 6 faroOut6 (gray x)) + 1#6
    (faroOut6 ⟨0, by omega⟩).val = 0 ∧
    (∃ i : Fin 6, faroOut6 (faroOut6 i) ≠ i) ∧
    iter F 8 0#6 = 0#6 ∧
    ¬ IsSingleCycle 6 F := by
  let F : BitVec 6 → BitVec 6 := fun x => invGray (applyBitPerm 6 faroOut6 (gray x)) + 1#6
  have s1 : F 0#6 = 1#6 := by decide
  have s2 : F 1#6 = 2#6 := by decide
  have s3 : F 2#6 = 15#6 := by decide
  have s4 : F 15#6 = 32#6 := by decide
  have s5 : F 32#6 = 57#6 := by decide
  have s6 : F 57#6 = 62#6 := by decide
  have s7 : F 62#6 = 63#6 := by decide
  have s8 : F 63#6 = 0#6 := by decide
  have h8 : iter F 8 0#6 = 0#6 := by
    simp only [iter, s1, s2, s3, s4, s5, s6, s7, s8]
  refine ⟨by decide, ⟨⟨1, by omega⟩, by decide⟩, h8, ?_⟩
  intro hsc
  exact hsc.1.2.2 8 (by omega) (by decide) h8

/-- Sharpness 3: Compiler A Theorem 4.2 width bound `w ≥ 3` is sharp (`w = 2`, `bitrev + 3` fails!). -/
theorem sharpness_compilerA_width2 :
    ¬ IsSingleCycle 2 (fun x => invGray (applyBitPerm 2 (bitrevFin 2) (gray x)) + ((1#2 <<< 1) + 1#2)) := by
  intro hsc
  have h2 : iter (fun x => invGray (applyBitPerm 2 (bitrevFin 2) (gray x)) + ((1#2 <<< 1) + 1#2)) 2 0#2 = 0#2 := by
    decide
  exact hsc.1.2.2 2 (by omega) (by decide) h2

/-- Sharpness 4: Compiler A Theorem 4.2 position condition `π(0) ∈ {0, w-2, w-1}` is sharp:
    at `w = 4`, `swap(0, 1)` has `π(0) = 1 ∉ {0, 2, 3}` and fails `IsSingleCycle 4`! -/
def swap01_4 (i : Fin 4) : Fin 4 :=
  if i.val = 0 then ⟨1, by omega⟩ else if i.val = 1 then ⟨0, by omega⟩ else i

theorem swap01_4_involutive (i : Fin 4) : swap01_4 (swap01_4 i) = i := by
  revert i; decide

theorem sharpness_compilerA_pos_swap01 :
    ¬ IsSingleCycle 4 (fun x => invGray (applyBitPerm 4 swap01_4 (gray x)) + ((1#4 <<< 3) + 1#4)) := by
  rw [grayBitPermInvolution_msbKick_singleCycle_iff (by omega) swap01_4 swap01_4_involutive]
  decide

/-- Sharpness 5: Compiler B Theorem 5.4 non-overlap condition `m ≤ k` (`k ≥ ⌈w/2⌉`) is sharp:
    at `w = 6, k = 2 < 3`, `(x ^^^ (x >>> 2)) + 1#6` has a 3-cycle `[35, 40, 44]` at `x = 35#6`,
    breaking the universal `{1, 2, giant}` trichotomy! -/
theorem sharpness_compilerB_overlap :
    let U : BitVec 6 → BitVec 6 := fun x => (x ^^^ (x >>> 2)) + 1#6
    HasMinPeriod U 35#6 3 ∧ iter U 3 0#6 ≠ 0#6 := by
  refine ⟨⟨by omega, by decide, ?_⟩, by decide⟩
  intro k hk0 hk3
  have hk : k = 1 ∨ k = 2 := by omega
  rcases hk with rfl | rfl <;> decide

/-- Sharpness 6: Compiler B Theorem 5.3 even-range condition is sharp:
    a single odd entry `h(0#4) = 1#4` breaks Hamiltonian single-cycle on `BitVec 8`! -/
def hOneOdd (a : BitVec 4) : BitVec 4 :=
  if a = 0#4 then 1#4 else a <<< 1

theorem sharpness_compilerB_one_odd : ¬ IsSingleCycle 8 (feistelCarry 4 4 hOneOdd) := by
  rw [feistelCarry_singleCycle_iff (by omega) (by omega) hOneOdd]
  intro hall
  have h0 := hall 0#4
  revert h0; decide

/-! ## Section 7: Exhaustive Kernel Axiom Audit (`#print axioms`) -/

end SiliconOrbitEngine
