/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NlfsrHolonomyLassoDebruijn.Defs

/-
  Standalone Lean 4.34.1 Verification of Task 12 (dynsil-12):
  Hybrid Carry-AND NLFSR De Bruijn & Period-Doubling Engine.

  Zero external dependencies (no Mathlib, no Lake).
  Zero `sorry`, zero custom axioms.

  ARCHITECTURE:
    Part I   : Pure-Silicon Bitwise & Finite XOR-Sum Primitives
    Part II  : Engine 1 — SliceHolonomyEngine (Exact Period-Doubling, Cycle-Splitting & Cylinder Lifting)
    Part III : Engine 2 — F2CarryTransducer & LassoCert Compiler (Finite-State F_2 Eigencycle -> Infinite Width)
    Part IV  : Engine 3 — Any-Bit-Blind Pairing Annihilator, Carry Parity Conservation & Return-Map Reduction
    Part V   : Infinite Theorems 1, 1b, 2 (a/b/c), 3 (a/b) + Non-Vacuity & Sharpness Witnesses + `#print axioms`
-/


-- ============================================================================
-- PART I: PURE-SILICON BITWISE & FINITE XOR-SUM PRIMITIVES
-- ============================================================================

namespace DynSil12

theorem iter_zero (f : Nat → Nat) (x : Nat) : iter f 0 x = x := rfl

theorem iter_succ (f : Nat → Nat) (n x : Nat) :
    iter f (n + 1) x = f (iter f n x) := rfl

theorem iter_add (f : Nat → Nat) (a b x : Nat) :
    iter f (a + b) x = iter f b (iter f a x) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [Nat.add_succ, iter_succ, iter_succ, ih]

theorem iter_succ_left (f : Nat → Nat) (n x : Nat) :
    iter f (n + 1) x = iter f n (f x) := by
  have h : n + 1 = 1 + n := Nat.add_comm n 1
  rw [h, iter_add]; rfl

theorem causal_mod {f : Nat → Nat} (hf : Causal f) (w x : Nat) :
    f (x % 2 ^ w) % 2 ^ w = f x % 2 ^ w :=
  hf w (x % 2 ^ w) x (Nat.mod_mod _ _)

theorem causal_iter {f : Nat → Nat} (hf : Causal f) (w t x y : Nat) (h : x % 2 ^ w = y % 2 ^ w) :
    iter f t x % 2 ^ w = iter f t y % 2 ^ w := by
  induction t with
  | zero => exact h
  | succ t ih => exact hf w _ _ ih

theorem causal_iter_mul_period {f : Nat → Nat} (hf : Causal f) (w x L : Nat)
    (hL : iter f L x % 2 ^ w = x % 2 ^ w) (k : Nat) :
    iter f (k * L) x % 2 ^ w = x % 2 ^ w := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    rw [Nat.succ_mul, iter_add]
    calc iter f L (iter f (k * L) x) % 2 ^ w
        = iter f L x % 2 ^ w := causal_iter hf w L _ _ ih
      _ = x % 2 ^ w := hL

theorem causal_period_dvd {f : Nat → Nat} (hf : Causal f) {w x L t : Nat}
    (hp : ExactPeriod f w x L) (ht : iter f t x % 2 ^ w = x % 2 ^ w) :
    L ∣ t := by
  rcases hp with ⟨hLpos, hLper, hmin⟩
  have hrem : iter f (t % L) x % 2 ^ w = x % 2 ^ w := by
    have hdiv : L * (t / L) + t % L = t := Nat.div_add_mod t L
    have h1 : iter f (t / L * L) x % 2 ^ w = x % 2 ^ w :=
      causal_iter_mul_period hf w x L hLper (t / L)
    have h2 : iter f t x % 2 ^ w = iter f (t % L) (iter f (t / L * L) x) % 2 ^ w := by
      rw [← iter_add, Nat.mul_comm (t / L) L, hdiv]
    rw [ht] at h2
    have h3 : iter f (t % L) (iter f (t / L * L) x) % 2 ^ w = iter f (t % L) x % 2 ^ w :=
      causal_iter hf w (t % L) _ _ h1
    rw [h3] at h2
    exact h2.symm
  by_cases h0 : t % L = 0
  · exact Nat.dvd_of_mod_eq_zero h0
  · exfalso
    exact hmin (t % L) (Nat.pos_of_ne_zero h0) (Nat.mod_lt t hLpos) hrem

/-- Clean characterization of `Nat.testBit` via division and mod 2. -/
theorem testBit_eq_div_mod (a w : Nat) :
    a.testBit w = ((a / 2 ^ w) % 2 == 1) := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
  have h : 1 &&& (a / 2 ^ w) = (a / 2 ^ w) % 2 := by
    rw [Nat.and_comm]; exact Nat.and_one_is_mod _
  rw [h]
  have hlt : (a / 2 ^ w) % 2 < 2 := Nat.mod_lt _ (by omega)
  cases hm : (a / 2 ^ w) % 2 with
  | zero => rfl
  | succ k =>
    have hk : k = 0 := by omega
    subst hk; rfl

/-- Exact bitwise mod-`2^w` equality via `testBit`. -/
theorem mod_two_pow_eq_iff (w a b : Nat) :
    a % 2 ^ w = b % 2 ^ w ↔ ∀ i < w, a.testBit i = b.testBit i := by
  constructor
  · intro h i hi
    have ha : (a % 2 ^ w).testBit i = a.testBit i := by
      rw [Nat.testBit_mod_two_pow]; simp [hi]
    have hb : (b % 2 ^ w).testBit i = b.testBit i := by
      rw [Nat.testBit_mod_two_pow]; simp [hi]
    rw [← ha, ← hb, h]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i < w
    · simp [hi, h i hi]
    · simp [hi]

theorem mod_two_pow_succ_eq_iff (w a b : Nat) :
    a % 2 ^ (w + 1) = b % 2 ^ (w + 1) ↔
    a % 2 ^ w = b % 2 ^ w ∧ a.testBit w = b.testBit w := by
  rw [mod_two_pow_eq_iff, mod_two_pow_eq_iff]
  constructor
  · intro h
    exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h w (Nat.lt_succ_self w)⟩
  · rintro ⟨hlo, hhi⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · exact hlo i hlt
    · exact hhi

/-- Fundamental carry-bit decomposition for `a + c` at bit `w`. -/
theorem testBit_add_decomp (a c w : Nat) :
    (a + c).testBit w = xor (a.testBit w) ((a % 2 ^ w + c).testBit w) := by
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
  have ha : a = 2 ^ w * (a / 2 ^ w) + a % 2 ^ w := (Nat.div_add_mod a (2 ^ w)).symm
  have hdiv : (a + c) / 2 ^ w = a / 2 ^ w + (a % 2 ^ w + c) / 2 ^ w := by
    conv => lhs; rw [ha, Nat.add_assoc]
    rw [Nat.mul_add_div hpos]
  rw [testBit_eq_div_mod, testBit_eq_div_mod, testBit_eq_div_mod, hdiv]
  have hsum : (a / 2 ^ w + (a % 2 ^ w + c) / 2 ^ w) % 2 =
              ((a / 2 ^ w) % 2 + ((a % 2 ^ w + c) / 2 ^ w) % 2) % 2 := Nat.add_mod _ _ 2
  rw [hsum]
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ w) with h1 | h1 <;>
  rcases Nat.mod_two_eq_zero_or_one ((a % 2 ^ w + c) / 2 ^ w) with h2 | h2 <;>
  simp [h1, h2]

/-- Basic Bool XOR algebraic laws. -/
theorem bxor_assoc (a b c : Bool) : xor (xor a b) c = xor a (xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bxor_comm (a b : Bool) : xor a b = xor b a := by
  cases a <;> cases b <;> rfl

theorem bxor_self (a : Bool) : xor a a = false := by
  cases a <;> rfl

theorem bxor_false (a : Bool) : xor a false = a := by
  cases a <;> rfl

theorem false_bxor (a : Bool) : xor false a = a := by
  cases a <;> rfl

/-- Finite XOR-sum over `0, 1, ..., n - 1`. -/
def xorRange : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, g => xor (xorRange n g) (g n)

theorem xorRange_add (a b : Nat) (g : Nat → Bool) :
    xorRange (a + b) g = xor (xorRange a g) (xorRange b (fun i => g (a + i))) := by
  induction b with
  | zero => simp [xorRange]
  | succ b ih =>
    rw [Nat.add_succ, xorRange, xorRange, ih, bxor_assoc]

theorem xorRange_congr {n : Nat} {g1 g2 : Nat → Bool}
    (h : ∀ i < n, g1 i = g2 i) : xorRange n g1 = xorRange n g2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorRange]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem xorRange_xor (n : Nat) (g1 g2 : Nat → Bool) :
    xorRange n (fun i => xor (g1 i) (g2 i)) = xor (xorRange n g1) (xorRange n g2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorRange, ih]
    cases xorRange n g1 <;> cases xorRange n g2 <;> cases g1 n <;> cases g2 n <;> rfl

theorem xorRange_false (n : Nat) : xorRange n (fun _ => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [xorRange, ih]

theorem xorRange_const (n : Nat) (b : Bool) :
    xorRange n (fun _ => b) = (if n % 2 == 1 then b else false) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorRange, ih]
    cases b <;> by_cases h : n % 2 = 1 <;> simp [h] <;> omega

/-- XOR over a `List Nat`, used for universal bijection / permutation invariance. -/
def xorList (g : Nat → Bool) : List Nat → Bool
  | [] => false
  | x :: xs => xor (g x) (xorList g xs)

theorem xorList_append (g : Nat → Bool) (l1 l2 : List Nat) :
    xorList g (l1 ++ l2) = xor (xorList g l1) (xorList g l2) := by
  induction l1 with
  | nil => simp [xorList]
  | cons x xs ih => simp [xorList, ih]

theorem xorRange_eq_xorList (n : Nat) (g : Nat → Bool) :
    xorRange n g = xorList g (List.range n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, xorList_append, xorRange, ih]
    simp [xorList]

theorem xorList_filter (pred g : Nat → Bool) (ls : List Nat) :
    xorList (fun y => if pred y = true then g y else false) ls =
    xorList g (ls.filter pred) := by
  induction ls with
  | nil => rfl
  | cons u us ih =>
    simp only [xorList, List.filter_cons]
    cases hpu : pred u
    · simp only [Bool.false_eq_true, ↓reduceIte, false_bxor]
      exact ih
    · simp only [↓reduceIte, xorList]
      rw [ih]

theorem nodup_filter (pred : Nat → Bool) {ls : List Nat} (h : ls.Nodup) :
    (ls.filter pred).Nodup := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    simp only [List.filter_cons]
    cases pred x
    · exact ih h.2
    · simp only [↓reduceIte, List.nodup_cons]
      exact ⟨fun hm => h.1 (List.mem_filter.mp hm).1, ih h.2⟩

theorem nodup_map_on {f : Nat → Nat} {ls : List Nat}
    (hinj : ∀ a ∈ ls, ∀ b ∈ ls, f a = f b → a = b) (hnd : ls.Nodup) :
    (ls.map f).Nodup := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (fun a ha b hb heq => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) heq) hnd.2⟩
    intro hm
    rcases List.mem_map.mp hm with ⟨y, hy, hfy⟩
    have hyx : y = x := hinj y (List.mem_cons_of_mem _ hy) x List.mem_cons_self hfy
    exact hnd.1 (hyx ▸ hy)

/-- Helper: removing an element from a list flips `xorList` by `g a`. -/
def eraseFirst (a : Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => if x = a then xs else x :: eraseFirst a xs

theorem mem_eraseFirst_of_ne {a b : Nat} {l : List Nat} (hne : b ≠ a) (hb : b ∈ l) :
    b ∈ eraseFirst a l := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    simp only [eraseFirst]
    split
    · subst_vars
      rcases List.mem_cons.mp hb with rfl | hxs
      · exact absurd rfl hne
      · exact hxs
    · rcases List.mem_cons.mp hb with rfl | hxs
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hxs)

theorem mem_of_mem_eraseFirst {a b : Nat} {l : List Nat} (hb : b ∈ eraseFirst a l) :
    b ∈ l := by
  induction l with
  | nil => simp [eraseFirst] at hb
  | cons x xs ih =>
    simp only [eraseFirst] at hb
    split at hb
    · exact List.mem_cons_of_mem _ hb
    · rcases List.mem_cons.mp hb with rfl | hxs
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hxs)

theorem not_mem_eraseFirst_of_nodup {a : Nat} {l : List Nat} (hnd : l.Nodup) :
    a ∉ eraseFirst a l := by
  induction l with
  | nil => simp [eraseFirst]
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    simp only [eraseFirst]
    split
    · subst_vars; exact hnd.1
    · rename_i hne
      intro hm
      rcases List.mem_cons.mp hm with rfl | hxs
      · exact hne rfl
      · exact ih hnd.2 hxs

theorem nodup_eraseFirst {a : Nat} {l : List Nat} (hnd : l.Nodup) :
    (eraseFirst a l).Nodup := by
  induction l with
  | nil => simp [eraseFirst]
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    simp only [eraseFirst]
    split
    · exact hnd.2
    · rw [List.nodup_cons]
      exact ⟨fun h => hnd.1 (mem_of_mem_eraseFirst h), ih hnd.2⟩

theorem length_eraseFirst {a : Nat} {l : List Nat} (ha : a ∈ l) :
    (eraseFirst a l).length + 1 = l.length := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    simp only [eraseFirst]
    split
    · simp
    · rename_i hne
      rcases List.mem_cons.mp ha with rfl | hxs
      · exact absurd rfl hne
      · simp [ih hxs]

theorem xorList_eraseFirst (g : Nat → Bool) {a : Nat} {l : List Nat} (ha : a ∈ l) :
    xor (g a) (xorList g (eraseFirst a l)) = xorList g l := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    simp only [eraseFirst, xorList]
    split
    · subst_vars; rfl
    · rename_i hne
      rcases List.mem_cons.mp ha with rfl | hxs
      · exact absurd rfl hne
      · simp only [xorList]
        rw [← bxor_assoc, bxor_comm (g a) (g x), bxor_assoc, ih hxs]

/-- Permutation invariance of `xorList` for any two `Nodup` lists with identical membership. -/
theorem xorList_eq_of_mem_iff (g : Nat → Bool) {l1 l2 : List Nat}
    (h1 : l1.Nodup) (h2 : l2.Nodup) (hmem : ∀ a, a ∈ l1 ↔ a ∈ l2) :
    xorList g l1 = xorList g l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons y ys =>
      have : y ∈ ([] : List Nat) := (hmem y).mpr List.mem_cons_self
      contradiction
  | cons x xs ih =>
    rw [List.nodup_cons] at h1
    have hx2 : x ∈ l2 := (hmem x).mp List.mem_cons_self
    rw [xorList, ← xorList_eraseFirst g hx2]
    congr 1
    apply ih h1.2 (nodup_eraseFirst h2)
    intro a
    constructor
    · intro hax
      have hne : a ≠ x := fun heq => h1.1 (heq ▸ hax)
      exact mem_eraseFirst_of_ne hne ((hmem a).mp (List.mem_cons_of_mem _ hax))
    · intro hae
      have hne : a ≠ x := fun heq => not_mem_eraseFirst_of_nodup h2 (heq ▸ hae)
      have ha1 : a ∈ x :: xs := (hmem a).mpr (mem_of_mem_eraseFirst hae)
      rcases List.mem_cons.mp ha1 with rfl | hxs
      · exact absurd rfl hne
      · exact hxs

/-- Finite pigeonhole: a `Nodup` sublist of equal length has identical membership. -/
theorem mem_iff_of_subset_eq_length {l1 l2 : List Nat}
    (h1 : l1.Nodup) (h2 : l2.Nodup) (hsub : ∀ a ∈ l1, a ∈ l2) (hlen : l1.length = l2.length) :
    ∀ a, a ∈ l1 ↔ a ∈ l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => intro a; rfl
    | cons y ys => simp at hlen
  | cons x xs ih =>
    rw [List.nodup_cons] at h1
    have hx2 : x ∈ l2 := hsub x List.mem_cons_self
    have hlen' : xs.length = (eraseFirst x l2).length := by
      have hle := length_eraseFirst hx2
      simp only [List.length_cons] at hlen
      omega
    have hsub' : ∀ a ∈ xs, a ∈ eraseFirst x l2 := by
      intro a ha
      have hne : a ≠ x := fun heq => h1.1 (heq ▸ ha)
      exact mem_eraseFirst_of_ne hne (hsub a (List.mem_cons_of_mem _ ha))
    have heq := ih h1.2 (nodup_eraseFirst h2) hsub' hlen'
    intro a
    by_cases hax : a = x
    · subst hax; exact ⟨fun _ => hx2, fun _ => List.mem_cons_self⟩
    · constructor
      · intro ha1; exact hsub a ha1
      · intro ha2
        exact List.mem_cons_of_mem _ ((heq a).mpr (mem_eraseFirst_of_ne hax ha2))

/-- Master XOR-sum bijection theorem on filtered ranges. -/
theorem xorRange_eq_filtered_of_inj {M N : Nat} (orb : Nat → Nat) (pred : Nat → Bool) (g : Nat → Bool)
    (h_in : ∀ t < M, orb t < N ∧ pred (orb t) = true)
    (h_inj : ∀ t1 t2, t1 < M → t2 < M → orb t1 = orb t2 → t1 = t2)
    (h_cnt : ((List.range N).filter pred).length = M) :
    xorRange M (fun t => g (orb t)) = xorRange N (fun y => if pred y then g y else false) := by
  let l1 := (List.range M).map orb
  let l2 := (List.range N).filter pred
  have h1_nd : l1.Nodup :=
    nodup_map_on (fun t1 ht1 t2 ht2 heq =>
      h_inj t1 t2 (List.mem_range.mp ht1) (List.mem_range.mp ht2) heq) List.nodup_range
  have h2_nd : l2.Nodup := nodup_filter pred List.nodup_range
  have hsub : ∀ a ∈ l1, a ∈ l2 := by
    intro a ha
    rcases List.mem_map.mp ha with ⟨t, ht, rfl⟩
    have htm := List.mem_range.mp ht
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (h_in t htm).1, (h_in t htm).2⟩
  have hlen : l1.length = l2.length := by
    simp [l1, l2, h_cnt]
  have hmem := mem_iff_of_subset_eq_length h1_nd h2_nd hsub hlen
  have hxl := xorList_eq_of_mem_iff g h1_nd h2_nd hmem
  have hleft : xorRange M (fun t => g (orb t)) = xorList g l1 := by
    rw [xorRange_eq_xorList]
    have : ∀ (ls : List Nat), xorList (fun t => g (orb t)) ls = xorList g (ls.map orb) := by
      intro ls; induction ls with
      | nil => rfl
      | cons u us ih => simp [xorList, ih]
    exact this (List.range M)
  have hright : xorRange N (fun y => if pred y then g y else false) = xorList g l2 := by
    rw [xorRange_eq_xorList]
    exact xorList_filter pred g (List.range N)
  rw [hleft, hright, hxl]

-- ============================================================================
-- PART II: ENGINE 1 — SLICE HOLONOMY ENGINE (EXACT LIFTING DICHOTOMY)
-- ============================================================================

/-- Cycle holonomy (monodromy parity) of `f` at bit `w` over `L` steps from `x`. -/
def cycleHolonomy (f : Nat → Nat) (delta : Nat → Nat → Bool) (w x L : Nat) : Bool :=
  xorRange L (fun t => delta w (iter f t x % 2 ^ w))

/-- Exact bit-`w` evolution along any orbit of a bit-sliced invertible map. -/
theorem iter_testBit_eq {f : Nat → Nat} {delta : Nat → Nat → Bool}
    (hf : BitSlicedInvertible f delta) (w x t : Nat) :
    (iter f t x).testBit w = xor (x.testBit w) (cycleHolonomy f delta w x t) := by
  induction t with
  | zero => simp [iter, cycleHolonomy, xorRange]
  | succ t ih =>
    rw [iter_succ, hf.2, ih, cycleHolonomy, cycleHolonomy, xorRange, bxor_assoc]

theorem cycleHolonomy_mod_eq {f : Nat → Nat} {delta : Nat → Nat → Bool}
    (hf : BitSlicedInvertible f delta) (w x y L : Nat) (h : x % 2 ^ w = y % 2 ^ w) :
    cycleHolonomy f delta w x L = cycleHolonomy f delta w y L := by
  apply xorRange_congr
  intro t _
  rw [causal_iter hf.1 w t x y h]

/-- ENGINE 1A (Exact Period-Doubling Law):
    If `x` has exact minimal period `L` mod `2^w` and `cycleHolonomy = true`,
    then `x` has exact minimal period `2 * L` mod `2^(w + 1)`. -/
theorem exactPeriod_lift_double {f : Nat → Nat} {delta : Nat → Nat → Bool}
    (hf : BitSlicedInvertible f delta) {w x L : Nat}
    (hp : ExactPeriod f w x L) (hhol : cycleHolonomy f delta w x L = true) :
    ExactPeriod f (w + 1) x (2 * L) := by
  rcases hp with ⟨hLpos, hLper, hmin⟩
  refine ⟨by omega, ?_, ?_⟩
  · rw [mod_two_pow_succ_eq_iff]
    constructor
    · exact causal_iter_mul_period hf.1 w x L hLper 2
    · rw [Nat.two_mul, iter_add, iter_testBit_eq hf,
          cycleHolonomy_mod_eq hf w (iter f L x) x L hLper,
          iter_testBit_eq hf, hhol]
      cases x.testBit w <;> rfl
  · intro t htpos htlt heq
    have hlo : iter f t x % 2 ^ w = x % 2 ^ w := ((mod_two_pow_succ_eq_iff w _ _).mp heq).1
    have hdvd : L ∣ t := causal_period_dvd hf.1 ⟨hLpos, hLper, hmin⟩ hlo
    rcases hdvd with ⟨k, rfl⟩
    have hk_ge : k ≥ 1 := by
      cases k with
      | zero => simp at htpos
      | succ _ => omega
    have hk_lt : k < 2 := by
      rcases Nat.lt_or_ge k 2 with hlt | hge
      · exact hlt
      · exfalso
        have hle : 2 * L ≤ L * k := by
          rw [Nat.mul_comm L k]; exact Nat.mul_le_mul_right L hge
        omega
    have hk : k = 1 := by omega
    subst hk
    rw [Nat.mul_one] at heq
    have hbit := ((mod_two_pow_succ_eq_iff w _ _).mp heq).2
    rw [iter_testBit_eq hf, hhol] at hbit
    cases hb : x.testBit w <;> simp [hb] at hbit

/-- ENGINE 1B (Exact Cycle-Splitting Law):
    If `x` has exact minimal period `L` mod `2^w` and `cycleHolonomy = false`,
    then BOTH lifts `x` and `x ^^^ 2^w` have exact minimal period `L` mod `2^(w + 1)`,
    and their orbits mod `2^(w + 1)` are completely disjoint! -/
theorem exactPeriod_lift_split {f : Nat → Nat} {delta : Nat → Nat → Bool}
    (hf : BitSlicedInvertible f delta) {w x L : Nat}
    (hp : ExactPeriod f w x L) (hhol : cycleHolonomy f delta w x L = false) :
    ExactPeriod f (w + 1) x L ∧
    ExactPeriod f (w + 1) (x ^^^ 2 ^ w) L ∧
    (∀ t, iter f t x % 2 ^ (w + 1) ≠ (x ^^^ 2 ^ w) % 2 ^ (w + 1)) := by
  have hx_lo : (x ^^^ 2 ^ w) % 2 ^ w = x % 2 ^ w := by
    rw [mod_two_pow_eq_iff]
    intro i hi
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    have hne : w ≠ i := Nat.ne_of_gt hi
    simp [hne]
  have hx_bit : (x ^^^ 2 ^ w).testBit w = !(x.testBit w) := by
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    cases x.testBit w <;> simp
  have h1 : ExactPeriod f (w + 1) x L := by
    rcases hp with ⟨hLpos, hLper, hmin⟩
    refine ⟨hLpos, ?_, ?_⟩
    · rw [mod_two_pow_succ_eq_iff]
      refine ⟨hLper, ?_⟩
      rw [iter_testBit_eq hf, hhol, bxor_false]
    · intro t htpos htlt heq
      exact hmin t htpos htlt ((mod_two_pow_succ_eq_iff w _ _).mp heq).1
  have h2 : ExactPeriod f (w + 1) (x ^^^ 2 ^ w) L := by
    rcases hp with ⟨hLpos, hLper, hmin⟩
    refine ⟨hLpos, ?_, ?_⟩
    · rw [mod_two_pow_succ_eq_iff]
      refine ⟨?_, ?_⟩
      · rw [causal_iter hf.1 w L _ _ hx_lo, hLper, hx_lo]
      · rw [iter_testBit_eq hf, cycleHolonomy_mod_eq hf w _ _ L hx_lo, hhol, bxor_false]
    · intro t htpos htlt heq
      have hlo := ((mod_two_pow_succ_eq_iff w _ _).mp heq).1
      rw [causal_iter hf.1 w t _ _ hx_lo, hx_lo] at hlo
      exact hmin t htpos htlt hlo
  have hdisj : ∀ t, iter f t x % 2 ^ (w + 1) ≠ (x ^^^ 2 ^ w) % 2 ^ (w + 1) := by
    intro t heq
    have hlo := ((mod_two_pow_succ_eq_iff w _ _).mp heq).1
    rw [hx_lo] at hlo
    rcases causal_period_dvd hf.1 hp hlo with ⟨k, rfl⟩
    have hk_bit : ∀ m, (iter f (L * m) x).testBit w = x.testBit w := by
      intro m
      induction m with
      | zero => simp [iter]
      | succ m ih =>
        rw [Nat.mul_succ, iter_add, iter_testBit_eq hf]
        have hmod : iter f (L * m) x % 2 ^ w = x % 2 ^ w := by
          rw [Nat.mul_comm L m]; exact causal_iter_mul_period hf.1 w x L hp.2.1 m
        rw [cycleHolonomy_mod_eq hf w _ _ L hmod, hhol, bxor_false, ih]
    have hbit := ((mod_two_pow_succ_eq_iff w _ _).mp heq).2
    rw [hk_bit k, hx_bit] at hbit
    cases hb : x.testBit w <;> simp [hb] at hbit
  exact ⟨h1, h2, hdisj⟩

/-- Helper: count of elements in `0..2^w - 1` matching a `w0`-slice predicate `P` is `L0 * 2^(w - w0)`. -/
theorem filter_slice_length (P : Nat → Bool) (w0 : Nat) (d : Nat) :
    ((List.range (2 ^ (w0 + d))).filter (fun y => P (y % 2 ^ w0))).length =
    ((List.range (2 ^ w0)).filter (fun y => P (y % 2 ^ w0))).length * 2 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hsplit : List.range (2 ^ (w0 + (d + 1))) =
        List.range (2 ^ (w0 + d)) ++ (List.range (2 ^ (w0 + d))).map (fun y => 2 ^ (w0 + d) + y) := by
      have hpow : 2 ^ (w0 + (d + 1)) = 2 ^ (w0 + d) + 2 ^ (w0 + d) := by
        rw [← Nat.add_assoc, Nat.pow_succ, Nat.mul_two]
      rw [hpow, List.range_add]
    rw [hsplit, List.filter_append, List.length_append, List.filter_map]
    have hcomp : ((fun y => P (y % 2 ^ w0)) ∘ fun y => 2 ^ (w0 + d) + y) =
        (fun y => P (y % 2 ^ w0)) := by
      funext y
      simp only [Function.comp]
      have hdvd : 2 ^ w0 ∣ 2 ^ (w0 + d) := by
        rw [Nat.pow_add]; exact Nat.dvd_mul_right _ _
      rcases hdvd with ⟨q, hq⟩
      rw [hq, Nat.mul_add_mod]
    rw [hcomp, List.length_map, ih, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]

/-- Helper: orbit points up to exact period `L` are pairwise distinct mod `2^w`. -/
theorem orbit_inj_of_exactPeriod {f : Nat → Nat} (hf : Causal f) {w x L : Nat}
    (hp : ExactPeriod f w x L) :
    ∀ t1 t2, t1 < L → t2 < L → iter f t1 x % 2 ^ w = iter f t2 x % 2 ^ w → t1 = t2 := by
  have hcase : ∀ a b, a < b → b < L →
      iter f a x % 2 ^ w = iter f b x % 2 ^ w → False := by
    intro a b hab hblt hab_eq
    let shift := L - a
    have h1 : iter f (a + shift) x % 2 ^ w = iter f (b + shift) x % 2 ^ w := by
      rw [iter_add, iter_add]
      exact causal_iter hf w shift _ _ hab_eq
    have has : a + shift = L := Nat.add_sub_of_le (Nat.le_of_lt (Nat.lt_trans hab hblt))
    have hbs : b + shift = L + (b - a) := by omega
    rw [has, hp.2.1, hbs, iter_add] at h1
    have h2 : iter f (b - a) (iter f L x) % 2 ^ w = iter f (b - a) x % 2 ^ w :=
      causal_iter hf w (b - a) _ _ hp.2.1
    rw [h2] at h1
    exact hp.2.2 (b - a) (by omega) (by omega) h1.symm
  intro t1 t2 ht1 ht2 heq
  rcases Nat.lt_trichotomy t1 t2 with hlt | rfl | hgt
  · exact absurd heq (fun h => hcase t1 t2 hlt ht2 h)
  · rfl
  · exact absurd heq.symm (fun h => hcase t2 t1 hgt ht1 h)

/-- ENGINE 1C (Cylinder Period-Doubling Inductive Compiler):
    If `P` is an `f`-invariant `w0`-slice cylinder of size `L0` forming a single cycle at width `w0`,
    and the cylinder holonomy is `true` at EVERY width `w = w0 + d`,
    then for EVERY `d : Nat`, `x` has exact minimal period `L0 * 2^d` modulo `2^(w0 + d)`! -/
theorem cylinder_period_doubling {f : Nat → Nat} {delta : Nat → Nat → Bool}
    (hf : BitSlicedInvertible f delta)
    (P : Nat → Bool) (w0 L0 x : Nat)
    (hP_inv : ∀ y, P (y % 2 ^ w0) = true → P (f y % 2 ^ w0) = true)
    (hP_cnt : ((List.range (2 ^ w0)).filter (fun y => P (y % 2 ^ w0))).length = L0)
    (hx_in : P (x % 2 ^ w0) = true)
    (hbase : ExactPeriod f w0 x L0)
    (hhol_all : ∀ d, xorRange (2 ^ (w0 + d))
      (fun y => if P (y % 2 ^ w0) then delta (w0 + d) y else false) = true) :
    ∀ d, ExactPeriod f (w0 + d) x (L0 * 2 ^ d) := by
  have horb_P : ∀ t, P (iter f t x % 2 ^ w0) = true := by
    intro t; induction t with
    | zero => exact hx_in
    | succ t iht => exact hP_inv _ iht
  intro d
  induction d with
  | zero => simpa using hbase
  | succ d ih =>
    have hstep_per : ExactPeriod f (w0 + d + 1) x (2 * (L0 * 2 ^ d)) := by
      apply exactPeriod_lift_double hf ih
      rw [cycleHolonomy]
      have horb_in : ∀ t < L0 * 2 ^ d,
          iter f t x % 2 ^ (w0 + d) < 2 ^ (w0 + d) ∧
          P ((iter f t x % 2 ^ (w0 + d)) % 2 ^ w0) = true := by
        intro t _
        refine ⟨Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
        have hmod : (iter f t x % 2 ^ (w0 + d)) % 2 ^ w0 = iter f t x % 2 ^ w0 :=
          Nat.mod_mod_of_dvd _ (by rw [Nat.pow_add]; exact Nat.dvd_mul_right _ _)
        rw [hmod]; exact horb_P t
      have horb_inj := orbit_inj_of_exactPeriod hf.1 ih
      have hcnt : ((List.range (2 ^ (w0 + d))).filter (fun y => P (y % 2 ^ w0))).length = L0 * 2 ^ d := by
        rw [filter_slice_length, hP_cnt]
      rw [xorRange_eq_filtered_of_inj (fun t => iter f t x % 2 ^ (w0 + d))
          (fun y => P (y % 2 ^ w0)) (delta (w0 + d)) horb_in horb_inj hcnt]
      exact hhol_all d
    have hmul : 2 * (L0 * 2 ^ d) = L0 * 2 ^ (d + 1) := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm 2 L0, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ d)]
    have hadd : w0 + d + 1 = w0 + (d + 1) := Nat.add_assoc w0 d 1
    rw [hmul, hadd] at hstep_per
    exact hstep_per

/-- Shifting the starting point along an orbit preserves exact minimal period. -/
theorem exactPeriod_of_mem_orbit {f : Nat → Nat} (hf : Causal f) {w x L : Nat}
    (hp : ExactPeriod f w x L) (k : Nat) :
    ExactPeriod f w (iter f k x) L := by
  rcases hp with ⟨hLpos, hLper, hmin⟩
  refine ⟨hLpos, ?_, ?_⟩
  · rw [← iter_add, Nat.add_comm k L, iter_add]
    exact causal_iter hf w k _ _ hLper
  · intro t htpos htlt heq
    let r := k % L
    let shift := L - r
    have h1 : iter f (k + t + shift) x % 2 ^ w = iter f (k + shift) x % 2 ^ w := by
      rw [iter_add, iter_add, iter_add]
      exact causal_iter hf w shift _ _ heq
    have hks : k + shift = (k / L + 1) * L := by
      have hdm : L * (k / L) + k % L = k := Nat.div_add_mod k L
      have hrl : r < L := Nat.mod_lt k hLpos
      simp only [shift, r]
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (k / L) L]
      omega
    have hkts : k + t + shift = (k / L + 1) * L + t := by omega
    rw [hkts, hks, iter_add] at h1
    have hper_q : iter f ((k / L + 1) * L) x % 2 ^ w = x % 2 ^ w :=
      causal_iter_mul_period hf w x L hLper (k / L + 1)
    rw [causal_iter hf w t _ _ hper_q, hper_q] at h1
    exact hmin t htpos htlt h1

/-- Every element in a single-cycle cylinder inherits the exact minimal period. -/
theorem exactPeriod_of_cylinder_mem {f : Nat → Nat} (hf : Causal f)
    {P : Nat → Bool} {w0 d L0 x y : Nat}
    (hP_inv : ∀ z, P (z % 2 ^ w0) = true → P (f z % 2 ^ w0) = true)
    (hP_cnt : ((List.range (2 ^ w0)).filter (fun z => P (z % 2 ^ w0))).length = L0)
    (hx_in : P (x % 2 ^ w0) = true) (hy_in : P (y % 2 ^ w0) = true)
    (hp : ExactPeriod f (w0 + d) x (L0 * 2 ^ d)) :
    ExactPeriod f (w0 + d) y (L0 * 2 ^ d) := by
  have horb_P : ∀ t, P (iter f t x % 2 ^ w0) = true := by
    intro t; induction t with
    | zero => exact hx_in
    | succ t iht => exact hP_inv _ iht
  let l1 := (List.range (L0 * 2 ^ d)).map (fun t => iter f t x % 2 ^ (w0 + d))
  let l2 := (List.range (2 ^ (w0 + d))).filter (fun z => P (z % 2 ^ w0))
  have h1_nd : l1.Nodup :=
    nodup_map_on (fun t1 ht1 t2 ht2 heq =>
      orbit_inj_of_exactPeriod hf hp t1 t2 (List.mem_range.mp ht1) (List.mem_range.mp ht2) heq)
      List.nodup_range
  have h2_nd : l2.Nodup := nodup_filter _ List.nodup_range
  have hsub : ∀ a ∈ l1, a ∈ l2 := by
    intro a ha
    rcases List.mem_map.mp ha with ⟨t, _, rfl⟩
    refine List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.mod_lt _ (Nat.two_pow_pos _)), ?_⟩
    have hmod : (iter f t x % 2 ^ (w0 + d)) % 2 ^ w0 = iter f t x % 2 ^ w0 :=
      Nat.mod_mod_of_dvd _ (by rw [Nat.pow_add]; exact Nat.dvd_mul_right _ _)
    rw [hmod]; exact horb_P t
  have hlen : l1.length = l2.length := by
    simp [l1, l2, filter_slice_length, hP_cnt]
  have hmem := mem_iff_of_subset_eq_length h1_nd h2_nd hsub hlen
  have hy_l2 : y % 2 ^ (w0 + d) ∈ l2 := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.mod_lt _ (Nat.two_pow_pos _)), ?_⟩
    have hmod : (y % 2 ^ (w0 + d)) % 2 ^ w0 = y % 2 ^ w0 :=
      Nat.mod_mod_of_dvd _ (by rw [Nat.pow_add]; exact Nat.dvd_mul_right _ _)
    rw [hmod]; exact hy_in
  rcases List.mem_map.mp ((hmem _).mpr hy_l2) with ⟨k, _, hk⟩
  have hpk := exactPeriod_of_mem_orbit hf hp k
  refine ⟨hpk.1, ?_, ?_⟩
  · rw [← causal_iter hf (w0 + d) (L0 * 2 ^ d) (iter f k x) y hk, hpk.2.1, hk]
  · intro t htpos htlt heq
    rw [← causal_iter hf (w0 + d) t (iter f k x) y hk, ← hk] at heq
    exact hpk.2.2 t htpos htlt heq

/-- Full-space De Bruijn specialization: if `ExactPeriod f w 0 (2^w)`, then `SingleCycle f w`. -/
theorem singleCycle_of_zero {f : Nat → Nat} (hf : Causal f) {w : Nat}
    (h0 : ExactPeriod f w 0 (2 ^ w)) : SingleCycle f w := by
  intro y
  have h := exactPeriod_of_cylinder_mem hf (P := fun _ => true) (w0 := 0) (d := w) (L0 := 1) (x := 0) (y := y)
    (fun _ _ => rfl) (by decide) rfl rfl (by simpa using h0)
  simpa using h

-- ============================================================================
-- PART III: ENGINE 2 — F_2 CARRY-TRANSDUCER EIGENCYCLE COMPILER
-- ============================================================================

theorem runTransducer_lt {S : Nat} {T : CarryTransducer S} (hV : T.Valid) (w x : Nat) :
    runTransducer T w x < S := by
  induction w with
  | zero => exact hV.1
  | succ w ih => exact hV.2 _ ih _

theorem runTransducer_mod {S : Nat} (T : CarryTransducer S) (w x : Nat) :
    runTransducer T w (x % 2 ^ w) = runTransducer T w x := by
  suffices ∀ k ≤ w, runTransducer T k (x % 2 ^ w) = runTransducer T k x from this w (Nat.le_refl w)
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [runTransducer]
    rw [ih (Nat.le_of_succ_le hk), Nat.testBit_mod_two_pow]
    have hlt : k < w := hk
    simp [hlt]

theorem vecStepAux_xor {S : Nat} (T : CarryTransducer S) (u v k : Nat) :
    vecStepAux T (u ^^^ v) k = vecStepAux T u k ^^^ vecStepAux T v k := by
  induction k with
  | zero => simp [vecStepAux]
  | succ k ih =>
    simp only [vecStepAux, Nat.testBit_xor, ih]
    cases u.testBit k <;> cases v.testBit k <;> simp
    · apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_xor]
      cases (vecStepAux T u k).testBit i <;> cases (vecStepAux T v k).testBit i <;>
      cases (1 <<< T.next k false).testBit i <;> cases (1 <<< T.next k true).testBit i <;> rfl
    · apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_xor]
      cases (vecStepAux T u k).testBit i <;> cases (vecStepAux T v k).testBit i <;>
      cases (1 <<< T.next k false).testBit i <;> cases (1 <<< T.next k true).testBit i <;> rfl
    · apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_xor]
      cases (vecStepAux T u k).testBit i <;> cases (vecStepAux T v k).testBit i <;>
      cases (1 <<< T.next k false).testBit i <;> cases (1 <<< T.next k true).testBit i <;> rfl

theorem vecStep_xor {S : Nat} (T : CarryTransducer S) (u v : Nat) :
    vecStep T (u ^^^ v) = vecStep T u ^^^ vecStep T v :=
  vecStepAux_xor T u v S

theorem vecStep_zero {S : Nat} (T : CarryTransducer S) : vecStep T 0 = 0 := by
  suffices ∀ k, vecStepAux T 0 k = 0 from this S
  intro k; induction k with
  | zero => rfl
  | succ k ih => simp [vecStepAux, ih]

theorem testBit_one_shiftLeft (a b : Nat) : (1 <<< a).testBit b = (a == b) := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
  by_cases h : a = b
  · subst h; simp
  · simp [h]

theorem vecStepAux_unit {S : Nat} (T : CarryTransducer S) (s k : Nat) :
    vecStepAux T (1 <<< s) k =
    if s < k then (1 <<< T.next s false) ^^^ (1 <<< T.next s true) else 0 := by
  induction k with
  | zero => simp [vecStepAux]
  | succ k ih =>
    simp only [vecStepAux, testBit_one_shiftLeft, ih]
    by_cases hsk : s = k
    · subst hsk; simp
    · by_cases hlt : s < k
      · have hne : (s == k) = false := beq_false_of_ne hsk
        have hlt2 : s < k + 1 := Nat.lt_succ_of_lt hlt
        simp [hne, hlt, hlt2]
      · have hne : (s == k) = false := beq_false_of_ne hsk
        have hge : ¬(s < k + 1) := by omega
        simp [hne, hlt, hge]

theorem vecStep_unit {S : Nat} (T : CarryTransducer S) {s : Nat} (hs : s < S) :
    vecStep T (1 <<< s) = (1 <<< T.next s false) ^^^ (1 <<< T.next s true) := by
  simp [vecStep, vecStepAux_unit, hs]

theorem vecHolAux_xor {S : Nat} (T : CarryTransducer S) (u v k : Nat) :
    vecHolAux T (u ^^^ v) k = xor (vecHolAux T u k) (vecHolAux T v k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [vecHolAux, Nat.testBit_xor, ih]
    cases u.testBit k <;> cases v.testBit k <;>
    cases vecHolAux T u k <;> cases vecHolAux T v k <;> cases T.toggle k <;> rfl

theorem vecHol_xor {S : Nat} (T : CarryTransducer S) (u v : Nat) :
    vecHol T (u ^^^ v) = xor (vecHol T u) (vecHol T v) :=
  vecHolAux_xor T u v S

theorem vecHol_zero {S : Nat} (T : CarryTransducer S) : vecHol T 0 = false := by
  suffices ∀ k, vecHolAux T 0 k = false from this S
  intro k; induction k with
  | zero => rfl
  | succ k ih => simp [vecHolAux, ih]

theorem vecHolAux_unit {S : Nat} (T : CarryTransducer S) (s k : Nat) :
    vecHolAux T (1 <<< s) k = if s < k then T.toggle s else false := by
  induction k with
  | zero => simp [vecHolAux]
  | succ k ih =>
    simp only [vecHolAux, testBit_one_shiftLeft, ih]
    by_cases hsk : s = k
    · subst hsk; simp
    · by_cases hlt : s < k
      · have hne : (s == k) = false := beq_false_of_ne hsk
        have hlt2 : s < k + 1 := Nat.lt_succ_of_lt hlt
        simp [hne, hlt, hlt2]
      · have hne : (s == k) = false := beq_false_of_ne hsk
        have hge : ¬(s < k + 1) := by omega
        simp [hne, hlt, hge]

theorem vecHol_unit {S : Nat} (T : CarryTransducer S) {s : Nat} (hs : s < S) :
    vecHol T (1 <<< s) = T.toggle s := by
  simp [vecHol, vecHolAux_unit, hs]

theorem xorMaskRange_add (a b : Nat) (g : Nat → Nat) :
    xorMaskRange (a + b) g = xorMaskRange a g ^^^ xorMaskRange b (fun i => g (a + i)) := by
  induction b with
  | zero => simp [xorMaskRange]
  | succ b ih =>
    rw [Nat.add_succ, xorMaskRange, xorMaskRange, ih, Nat.xor_assoc]

theorem xorMaskRange_congr {n : Nat} {g1 g2 : Nat → Nat}
    (h : ∀ i < n, g1 i = g2 i) : xorMaskRange n g1 = xorMaskRange n g2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorMaskRange]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem vecStep_xorMaskRange {S : Nat} (T : CarryTransducer S) (n : Nat) (g : Nat → Nat) :
    vecStep T (xorMaskRange n g) = xorMaskRange n (fun i => vecStep T (g i)) := by
  induction n with
  | zero => exact vecStep_zero T
  | succ n ih => simp only [xorMaskRange, vecStep_xor, ih]

theorem vecHol_xorMaskRange {S : Nat} (T : CarryTransducer S) (n : Nat) (g : Nat → Nat) :
    vecHol T (xorMaskRange n g) = xorRange n (fun i => vecHol T (g i)) := by
  induction n with
  | zero => exact vecHol_zero T
  | succ n ih => simp only [xorMaskRange, xorRange, vecHol_xor, ih]

/-- Fundamental F_2 Transfer Identity: lifting a cylinder by 1 bit applies `vecStep T`. -/
theorem cylinderVec_succ {S : Nat} {T : CarryTransducer S} (hV : T.Valid)
    (P : Nat → Bool) (w0 w : Nat) (hw : w0 ≤ w) :
    cylinderVec T P w0 (w + 1) = vecStep T (cylinderVec T P w0 w) := by
  unfold cylinderVec
  have hpow : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ, Nat.mul_two]
  rw [hpow, xorMaskRange_add, vecStep_xorMaskRange]
  have hcomb : ∀ n (a b : Nat → Nat),
      xorMaskRange n a ^^^ xorMaskRange n b = xorMaskRange n (fun i => a i ^^^ b i) := by
    intro n a b; induction n with
    | zero => simp [xorMaskRange]
    | succ n ih =>
      simp only [xorMaskRange, ← ih]
      apply Nat.eq_of_testBit_eq; intro j
      simp only [Nat.testBit_xor]
      cases (xorMaskRange n a).testBit j <;> cases (xorMaskRange n b).testBit j <;>
      cases (a n).testBit j <;> cases (b n).testBit j <;> rfl
  rw [hcomb]
  apply xorMaskRange_congr
  intro y hy
  have hbit_lo : y.testBit w = false := Nat.testBit_lt_two_pow hy
  have hbit_hi : (2 ^ w + y).testBit w = true := by
    rw [testBit_eq_div_mod]
    have hdiv : (2 ^ w + y) / 2 ^ w = 1 := by
      rw [Nat.add_div_left _ (Nat.two_pow_pos w)]
      have : y / 2 ^ w = 0 := Nat.div_eq_of_lt hy
      omega
    rw [hdiv]; rfl
  have hmod_hi : (2 ^ w + y) % 2 ^ w = y := by
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hy]
  have hmod_w0 : (2 ^ w + y) % 2 ^ w0 = y % 2 ^ w0 := by
    have hdvd : 2 ^ w0 ∣ 2 ^ w := Nat.pow_dvd_pow 2 hw
    rcases hdvd with ⟨q, hq⟩
    rw [hq, Nat.mul_add_mod]
  have hrun_hi : runTransducer T w (2 ^ w + y) = runTransducer T w y := by
    rw [← runTransducer_mod T w (2 ^ w + y), hmod_hi]
  simp only [runTransducer, hbit_lo, hbit_hi, hmod_w0, hrun_hi]
  cases P (y % 2 ^ w0)
  · simp [vecStep_zero]
  · simp [vecStep_unit T (runTransducer_lt hV w y)]

/-- Fundamental F_2 Readout Identity: cylinder holonomy equals `vecHol T (cylinderVec ...)`. -/
theorem cylinderHol_eq_vecHol {S : Nat} {T : CarryTransducer S} (hV : T.Valid)
    (P : Nat → Bool) (w0 w : Nat) :
    xorRange (2 ^ w) (fun y => if P (y % 2 ^ w0) then T.toggle (runTransducer T w y) else false) =
    vecHol T (cylinderVec T P w0 w) := by
  unfold cylinderVec
  rw [vecHol_xorMaskRange]
  apply xorRange_congr
  intro y _
  cases P (y % 2 ^ w0)
  · simp [vecHol_zero]
  · simp [vecHol_unit T (runTransducer_lt hV w y)]

theorem checkChain_iter (step : Nat → Nat) (ls : List Nat) (v0 : Nat)
    (h : checkChain step ls v0 = true) :
    ∀ k (hk : k < ls.length), ls[k]'hk = iter step k v0 := by
  induction ls generalizing v0 with
  | nil => intro k hk; simp at hk
  | cons u us ih =>
    simp only [checkChain, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, hrest⟩
    intro k hk
    cases k with
    | zero => rfl
    | succ k =>
      simp only [List.getElem_cons_succ]
      rw [ih (step u) hrest k (Nat.lt_of_succ_lt_succ hk), iter_succ_left]

theorem list_length_pos {ls : List Nat} (hne : ls ≠ []) : 0 < ls.length := by
  cases ls with
  | nil => exact absurd rfl hne
  | cons _ _ => simp

theorem checkChain_last_step (step : Nat → Nat) (ls : List Nat) (v0 : Nat)
    (h : checkChain step ls v0 = true) (hne : ls ≠ []) :
    step (ls.getLast hne) = iter step ls.length v0 := by
  have hpos := list_length_pos hne
  have hlen : ls.length - 1 < ls.length := Nat.sub_lt hpos (by omega)
  have hget : ls.getLast hne = ls[ls.length - 1]'hlen := List.getLast_eq_getElem hne
  rw [hget, checkChain_iter step ls v0 h (ls.length - 1) hlen]
  have heq : ls.length = (ls.length - 1) + 1 := (Nat.sub_add_cancel hpos).symm
  conv => rhs; rw [heq, iter_succ]

theorem getLast_eq_getLast_bang (ls : List Nat) (hne : ls ≠ []) :
    ls.getLast! = ls.getLast hne := by
  cases ls with
  | nil => exact absurd rfl hne
  | cons _ _ => simp [List.getLast!]

theorem getLast_append_right (l1 l2 : List Nat) (hne2 : l2 ≠ []) (hne : l1 ++ l2 ≠ []) :
    (l1 ++ l2).getLast hne = l2.getLast hne2 := by
  induction l1 with
  | nil => rfl
  | cons x xs ih =>
    have hne' : xs ++ l2 ≠ [] := by
      intro h; apply hne2
      cases xs <;> simp at h; exact h
    simp only [List.cons_append]
    rw [List.getLast_cons hne', ih hne']

/-- MASTER COMPILER SOUNDNESS THEOREM:
    Any `LassoCert` passing `checkLasso T v0 cert = true` certifies that
    `vecHol T (iter (vecStep T) d v0) = true` for ALL `d : Nat`! -/
theorem lasso_cert_sound {S : Nat} (T : CarryTransducer S) (v0 : Nat) (cert : LassoCert)
    (hcert : checkLasso T v0 cert = true) :
    ∀ d, vecHol T (iter (vecStep T) d v0) = true := by
  cases hcyc : cert.cyc with
  | nil => simp [checkLasso, hcyc] at hcert
  | cons c0 cs =>
    simp only [checkLasso, hcyc, Bool.and_eq_true, beq_iff_eq] at hcert
    rcases hcert with ⟨⟨hchain, hloop⟩, hall⟩
    let full := cert.pre ++ (c0 :: cs)
    have hne_cyc : (c0 :: cs) ≠ [] := List.cons_ne_nil _ _
    have hne_full : full ≠ [] := by simp [full]
    have hlast_full : full.getLast hne_full = (c0 :: cs).getLast hne_cyc :=
      getLast_append_right cert.pre (c0 :: cs) hne_cyc hne_full
    have hlast_eq : (c0 :: cs).getLast! = (c0 :: cs).getLast hne_cyc :=
      getLast_eq_getLast_bang _ hne_cyc
    rw [hlast_eq] at hloop
    have hfull_eq : ∀ k (hk : k < full.length), full[k]'hk = iter (vecStep T) k v0 :=
      checkChain_iter (vecStep T) full v0 hchain
    have hpre_lt : cert.pre.length < full.length := by simp [full]
    have hc0_iter : c0 = iter (vecStep T) cert.pre.length v0 := by
      have h1 := hfull_eq cert.pre.length hpre_lt
      have h2 : full[cert.pre.length]'hpre_lt = c0 := by simp [full]
      rw [h2] at h1; exact h1
    have hloop_iter : iter (vecStep T) (cert.pre.length + (c0 :: cs).length) v0 =
                      iter (vecStep T) cert.pre.length v0 := by
      have hfl : full.length = cert.pre.length + (c0 :: cs).length := by simp [full]
      rw [← hfl, ← checkChain_last_step (vecStep T) full v0 hchain hne_full,
          hlast_full, hloop, hc0_iter]
    have hmem_full : ∀ d, iter (vecStep T) d v0 ∈ full := by
      intro d
      by_cases hlt : d < full.length
      · rw [← hfull_eq d hlt]; exact List.getElem_mem hlt
      · let p := cert.pre.length
        let q := (c0 :: cs).length
        have hqpos : q > 0 := by simp [q]
        have hdp : p ≤ d := by
          have hfl : full.length = p + q := by simp [full, p, q]
          omega
        let r := (d - p) % q
        let k := (d - p) / q
        have hdm : q * k + r = d - p := Nat.div_add_mod (d - p) q
        have hmul_comm : k * q = q * k := Nat.mul_comm k q
        have hd_eq : d = p + k * q + r := by omega
        have hstep_per : ∀ m, iter (vecStep T) (p + m * q) v0 = iter (vecStep T) p v0 := by
          intro m
          induction m with
          | zero => simp
          | succ m ihm =>
            have h1 : p + (m + 1) * q = (p + m * q) + q := by rw [Nat.succ_mul]; omega
            rw [h1, iter_add, ihm, ← iter_add]
            exact hloop_iter
        have heq_r : iter (vecStep T) d v0 = iter (vecStep T) (p + r) v0 := by
          rw [hd_eq, iter_add, hstep_per k, ← iter_add]
        have hpr_lt : p + r < full.length := by
          have hrlt : r < q := Nat.mod_lt _ hqpos
          have hfl : full.length = p + q := by simp [full, p, q]
          omega
        rw [heq_r, ← hfull_eq (p + r) hpr_lt]
        exact List.getElem_mem hpr_lt
    intro d
    exact List.all_eq_true.mp hall _ (hmem_full d)

/-- END-TO-END TRANSDUCER PERIOD-DOUBLING ENGINE:
    Connects a finite `LassoCert` directly to an infinite-width `ExactPeriod` theorem! -/
theorem transducer_cert_period_doubling {S : Nat} {f : Nat → Nat} {delta : Nat → Nat → Bool}
    (hf : BitSlicedInvertible f delta)
    (T : CarryTransducer S) (hV : T.Valid)
    (P : Nat → Bool) (w0 L0 x : Nat)
    (htrack : ∀ d y, y < 2 ^ (w0 + d) → P (y % 2 ^ w0) = true →
              delta (w0 + d) y = T.toggle (runTransducer T (w0 + d) y))
    (hP_inv : ∀ y, P (y % 2 ^ w0) = true → P (f y % 2 ^ w0) = true)
    (hP_cnt : ((List.range (2 ^ w0)).filter (fun y => P (y % 2 ^ w0))).length = L0)
    (hx_in : P (x % 2 ^ w0) = true)
    (hbase : ExactPeriod f w0 x L0)
    (cert : LassoCert)
    (hcert : checkLasso T (cylinderVec T P w0 w0) cert = true) :
    ∀ d, ExactPeriod f (w0 + d) x (L0 * 2 ^ d) := by
  have hvec_all : ∀ d, cylinderVec T P w0 (w0 + d) = iter (vecStep T) d (cylinderVec T P w0 w0) := by
    intro d; induction d with
    | zero => rfl
    | succ d ih =>
      rw [← Nat.add_assoc, cylinderVec_succ hV P w0 (w0 + d) (Nat.le_add_right w0 d), ih, iter_succ]
  apply cylinder_period_doubling hf P w0 L0 x hP_inv hP_cnt hx_in hbase
  intro d
  have hcongr :
      xorRange (2 ^ (w0 + d)) (fun y => if P (y % 2 ^ w0) then delta (w0 + d) y else false) =
      xorRange (2 ^ (w0 + d)) (fun y => if P (y % 2 ^ w0) then T.toggle (runTransducer T (w0 + d) y) else false) := by
    apply xorRange_congr
    intro y hy
    cases hpy : P (y % 2 ^ w0)
    · rfl
    · exact htrack d y hy hpy
  rw [hcongr, cylinderHol_eq_vecHol hV, hvec_all d]
  exact lasso_cert_sound T (cylinderVec T P w0 w0) cert hcert d

-- ============================================================================
-- PART IV: ENGINE 3 — ANY-BIT-BLIND PAIRING, CARRY PARITY & RETURN-MAP ENGINE
-- ============================================================================

/-- Any-Bit-Blind Pairing Involution Annihilator:
    If `g` on `0..2^w - 1` is invariant under flipping SOME bit `j < w`,
    then its full-cube XOR sum vanishes identically! -/
theorem any_bit_blind_xorRange_false {w j : Nat} (hj : j < w) (g : Nat → Bool)
    (hblind : ∀ y < 2 ^ w, g (y ^^^ 2 ^ j) = g y) :
    xorRange (2 ^ w) g = false := by
  have hsplit : xorRange (2 ^ w) g =
      xor (xorRange (2 ^ w) (fun y => if !y.testBit j then g y else false))
          (xorRange (2 ^ w) (fun y => if y.testBit j then g y else false)) := by
    rw [← xorRange_xor]
    apply xorRange_congr
    intro y _
    cases y.testBit j <;> simp
  rw [hsplit]
  let l0 := (List.range (2 ^ w)).filter (fun y => !y.testBit j)
  let l1 := (List.range (2 ^ w)).filter (fun y => y.testBit j)
  let l0_map := l0.map (fun y => y ^^^ 2 ^ j)
  have hlt_xor : ∀ y < 2 ^ w, y ^^^ 2 ^ j < 2 ^ w := by
    intro y hy
    have h2j : 2 ^ j < 2 ^ w := Nat.pow_lt_pow_right (by omega) hj
    exact Nat.xor_lt_two_pow hy h2j
  have hxor_inv : ∀ y, (y ^^^ 2 ^ j) ^^^ 2 ^ j = y := by
    intro y; rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have h0_nd : l0.Nodup := nodup_filter _ List.nodup_range
  have h1_nd : l1.Nodup := nodup_filter _ List.nodup_range
  have hm_nd : l0_map.Nodup :=
    nodup_map_on (fun a _ b _ heq => by
      have := congrArg (· ^^^ 2 ^ j) heq
      simpa [hxor_inv] using this) h0_nd
  have hmem : ∀ a, a ∈ l0_map ↔ a ∈ l1 := by
    intro a
    constructor
    · intro ha
      rcases List.mem_map.mp ha with ⟨y, hy, rfl⟩
      rcases List.mem_filter.mp hy with ⟨hyr, hyb⟩
      have hylt := List.mem_range.mp hyr
      refine List.mem_filter.mpr ⟨List.mem_range.mpr (hlt_xor y hylt), ?_⟩
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      simp at hyb; simp [hyb]
    · intro ha
      rcases List.mem_filter.mp ha with ⟨har, hab⟩
      have halt := List.mem_range.mp har
      refine List.mem_map.mpr ⟨a ^^^ 2 ^ j, ?_, hxor_inv a⟩
      refine List.mem_filter.mpr ⟨List.mem_range.mpr (hlt_xor a halt), ?_⟩
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      simp [hab]
  have hlist_eq : xorList g l0_map = xorList g l1 :=
    xorList_eq_of_mem_iff g hm_nd h1_nd hmem
  have hmap_eq : xorList g l0_map = xorList g l0 := by
    have : ∀ ls, (∀ y ∈ ls, y < 2 ^ w) → xorList g (ls.map (fun y => y ^^^ 2 ^ j)) = xorList g ls := by
      intro ls hls; induction ls with
      | nil => rfl
      | cons u us ih =>
        simp only [List.map_cons, xorList]
        rw [hblind u (hls u List.mem_cons_self),
            ih (fun v hv => hls v (List.mem_cons_of_mem _ hv))]
    exact this l0 (fun y hy => List.mem_range.mp (List.mem_filter.mp hy).1)
  have hleft : xorRange (2 ^ w) (fun y => if !y.testBit j then g y else false) = xorList g l0 := by
    rw [xorRange_eq_xorList]; exact xorList_filter (fun y => !y.testBit j) g (List.range (2 ^ w))
  have hright : xorRange (2 ^ w) (fun y => if y.testBit j then g y else false) = xorList g l1 := by
    rw [xorRange_eq_xorList]; exact xorList_filter (fun y => y.testBit j) g (List.range (2 ^ w))
  rw [hleft, hright, ← hlist_eq, hmap_eq, bxor_self]

/-- Carry Parity Conservation Law:
    For EVERY `w ≥ 1` and EVERY `c : Nat`, the full-cube carry-out XOR sum of `z + c` at bit `w`
    equals `c % 2 == 1`! -/
theorem carry_xorRange_parity {w : Nat} (hw : w ≥ 1) (c : Nat) :
    xorRange (2 ^ w) (fun z => (z + c).testBit w) = (c % 2 == 1) := by
  have hNpos : 0 < 2 ^ w := Nat.two_pow_pos w
  have hNeven : 2 ^ w % 2 = 0 := by
    have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
      have hw1 : w = (w - 1) + 1 := by omega
      conv => lhs; rw [hw1, Nat.pow_succ, Nat.mul_comm]
    omega
  let q := c / 2 ^ w
  let r := c % 2 ^ w
  have hrlt : r < 2 ^ w := Nat.mod_lt c hNpos
  have hc_eq : c = 2 ^ w * q + r := (Nat.div_add_mod c (2 ^ w)).symm
  have hsplit : 2 ^ w = (2 ^ w - r) + r := (Nat.sub_add_cancel (Nat.le_of_lt hrlt)).symm
  conv => lhs; rw [hsplit]
  rw [xorRange_add]
  have hlo : xorRange (2 ^ w - r) (fun z => (z + c).testBit w) =
             xorRange (2 ^ w - r) (fun _ => q % 2 == 1) := by
    apply xorRange_congr
    intro z hz
    rw [testBit_eq_div_mod]
    have hdiv : (z + c) / 2 ^ w = q := by
      rw [hc_eq]
      have : z + (2 ^ w * q + r) = (z + r) + 2 ^ w * q := by omega
      rw [this, Nat.add_mul_div_left _ _ hNpos, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    rw [hdiv]
  have hhi : xorRange r (fun i => ((2 ^ w - r) + i + c).testBit w) =
             xorRange r (fun _ => (q + 1) % 2 == 1) := by
    apply xorRange_congr
    intro i hi
    rw [testBit_eq_div_mod]
    have hdiv : ((2 ^ w - r) + i + c) / 2 ^ w = q + 1 := by
      rw [hc_eq]
      have : (2 ^ w - r) + i + (2 ^ w * q + r) = i + 2 ^ w * (q + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      rw [this, Nat.add_mul_div_left _ _ hNpos, Nat.div_eq_of_lt (Nat.lt_trans hi hrlt), Nat.zero_add]
    rw [hdiv]
  rw [hlo, hhi, xorRange_const, xorRange_const]
  have hr_mod2 : r % 2 = c % 2 := Nat.mod_mod_of_dvd c (Nat.dvd_of_mod_eq_zero hNeven)
  have hnr_mod2 : (2 ^ w - r) % 2 = c % 2 := by omega
  rw [hr_mod2, hnr_mod2]
  have hq1 : (q + 1) % 2 = (q % 2 + 1) % 2 := Nat.add_mod q 1 2
  rcases Nat.mod_two_eq_zero_or_one c with hc2 | hc2 <;>
  rcases Nat.mod_two_eq_zero_or_one q with hq2 | hq2 <;>
  simp [hc2, hq2, hq1]

/-- Full-cube XOR-sum invariance under any bijection `h` on `0 .. 2^w - 1`. -/
theorem xorRange_bij {w : Nat} (h : Nat → Nat) (g : Nat → Bool)
    (hinj : ∀ x y, x < 2 ^ w → y < 2 ^ w → h x % 2 ^ w = h y % 2 ^ w → x = y) :
    xorRange (2 ^ w) (fun x => g (h x % 2 ^ w)) = xorRange (2 ^ w) g := by
  have hres := xorRange_eq_filtered_of_inj
    (fun x => h x % 2 ^ w) (fun _ => true) g
    (fun t _ => ⟨Nat.mod_lt _ (Nat.two_pow_pos w), rfl⟩)
    hinj
    (by
      have hf : ∀ (ls : List Nat), ls.filter (fun _ => true) = ls := by
        intro ls; induction ls with
        | nil => rfl
        | cons _ _ ih => simp [ih]
      rw [hf, List.length_range])
  simpa only [↓reduceIte] using hres

/-- Every bit-sliced invertible map is injective modulo `2^w`! -/
theorem BitSlicedInvertible.inj_mod {f : Nat → Nat} {delta : Nat → Nat → Bool}
    (hf : BitSlicedInvertible f delta) (w : Nat) :
    ∀ x y, x < 2 ^ w → y < 2 ^ w → f x % 2 ^ w = f y % 2 ^ w → x = y := by
  induction w with
  | zero => intro x y hx hy _; omega
  | succ w ih =>
    intro x y hx hy heq
    have hlo_f : f x % 2 ^ w = f y % 2 ^ w :=
      ((mod_two_pow_succ_eq_iff w _ _).mp heq).1
    have hlo_f' : f (x % 2 ^ w) % 2 ^ w = f (y % 2 ^ w) % 2 ^ w := by
      rw [causal_mod hf.1, causal_mod hf.1]; exact hlo_f
    have hlo_xy : x % 2 ^ w = y % 2 ^ w :=
      ih (x % 2 ^ w) (y % 2 ^ w) (Nat.mod_lt _ (Nat.two_pow_pos w))
         (Nat.mod_lt _ (Nat.two_pow_pos w)) hlo_f'
    have hbit_f : (f x).testBit w = (f y).testBit w :=
      ((mod_two_pow_succ_eq_iff w _ _).mp heq).2
    rw [hf.2, hf.2, hlo_xy] at hbit_f
    have hbit_xy : x.testBit w = y.testBit w := by
      cases hx_b : x.testBit w <;> cases hy_b : y.testBit w <;>
      cases hd : delta w (y % 2 ^ w) <;> simp [hx_b, hy_b, hd] at hbit_f ⊢
    have hmod_eq : x % 2 ^ (w + 1) = y % 2 ^ (w + 1) :=
      (mod_two_pow_succ_eq_iff w x y).mpr ⟨hlo_xy, hbit_xy⟩
    rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hmod_eq
    exact hmod_eq

/-- ENGINE 3A (Finite-Slice Return-Map Period Multiplication Theorem):
    Given a causal map `f`, slice width `k0`, and base cycle `ExactPeriod f k0 r L` with `r < 2^k0`,
    define the upper-register return map `R q := iter f L (2^k0 * q + r) / 2^k0`.
    Then for EVERY `d : Nat` and EVERY `q : Nat`:
      `ExactPeriod R d q M → ExactPeriod f (k0 + d) (2^k0 * q + r) (L * M)`. -/
def returnMap (f : Nat → Nat) (k0 r L : Nat) (q : Nat) : Nat :=
  iter f L (2 ^ k0 * q + r) / 2 ^ k0

theorem returnMap_spec {f : Nat → Nat} (hf : Causal f) {k0 r L : Nat}
    (hL : iter f L r % 2 ^ k0 = r) (q : Nat) :
    iter f L (2 ^ k0 * q + r) = 2 ^ k0 * returnMap f k0 r L q + r := by
  have hmod : iter f L (2 ^ k0 * q + r) % 2 ^ k0 = r := by
    have h1 : (2 ^ k0 * q + r) % 2 ^ k0 = r % 2 ^ k0 := Nat.mul_add_mod _ _ _
    rw [causal_iter hf k0 L _ _ h1, hL]
  unfold returnMap
  have hdm := Nat.div_add_mod (iter f L (2 ^ k0 * q + r)) (2 ^ k0)
  rw [hmod] at hdm
  exact hdm.symm

theorem returnMap_iter {f : Nat → Nat} (hf : Causal f) {k0 r L : Nat}
    (hL : iter f L r % 2 ^ k0 = r) (t q : Nat) :
    iter f (t * L) (2 ^ k0 * q + r) = 2 ^ k0 * iter (returnMap f k0 r L) t q + r := by
  induction t with
  | zero => simp [iter]
  | succ t ih =>
    rw [Nat.succ_mul, iter_add, ih, returnMap_spec hf hL, iter_succ]

theorem returnMap_causal {f : Nat → Nat} (hf : Causal f) {k0 r L : Nat} :
    Causal (returnMap f k0 r L) := by
  intro d q1 q2 hq
  unfold returnMap
  have hmul : (2 ^ k0 * q1 + r) % 2 ^ (k0 + d) = (2 ^ k0 * q2 + r) % 2 ^ (k0 + d) := by
    have hpow : 2 ^ (k0 + d) = 2 ^ k0 * 2 ^ d := Nat.pow_add 2 k0 d
    have hq1 : 2 ^ k0 * q1 = 2 ^ (k0 + d) * (q1 / 2 ^ d) + 2 ^ k0 * (q1 % 2 ^ d) := by
      rw [hpow, Nat.mul_assoc, ← Nat.mul_add, Nat.div_add_mod]
    have hq2 : 2 ^ k0 * q2 = 2 ^ (k0 + d) * (q2 / 2 ^ d) + 2 ^ k0 * (q2 % 2 ^ d) := by
      rw [hpow, Nat.mul_assoc, ← Nat.mul_add, Nat.div_add_mod]
    rw [hq1, hq2, Nat.add_assoc, Nat.add_assoc, Nat.mul_add_mod, Nat.mul_add_mod, hq]
  have hit := causal_iter hf (k0 + d) L _ _ hmul
  have hdiv : ∀ a, (a / 2 ^ k0) % 2 ^ d = (a % 2 ^ (k0 + d)) / 2 ^ k0 := by
    intro a
    rw [Nat.pow_add, Nat.mod_mul_right_div_self]
  rw [hdiv, hdiv, hit]

theorem returnMap_exactPeriod {f : Nat → Nat} (hf : Causal f) {k0 r L d q M : Nat}
    (hr : r < 2 ^ k0) (hbase : ExactPeriod f k0 r L)
    (hR : ExactPeriod (returnMap f k0 r L) d q M) :
    ExactPeriod f (k0 + d) (2 ^ k0 * q + r) (L * M) := by
  have hL : iter f L r % 2 ^ k0 = r := by
    have h := hbase.2.1; rwa [Nat.mod_eq_of_lt hr] at h
  have hshift_eq : ∀ a b, (2 ^ k0 * a + r) % 2 ^ (k0 + d) = (2 ^ k0 * b + r) % 2 ^ (k0 + d) ↔
      a % 2 ^ d = b % 2 ^ d := by
    intro a b
    have hpow : 2 ^ (k0 + d) = 2 ^ k0 * 2 ^ d := Nat.pow_add 2 k0 d
    have ha : (2 ^ k0 * a + r) % (2 ^ k0 * 2 ^ d) = 2 ^ k0 * (a % 2 ^ d) + r := by
      have h1 : 2 ^ k0 * a + r = (2 ^ k0 * 2 ^ d) * (a / 2 ^ d) + (2 ^ k0 * (a % 2 ^ d) + r) := by
        rw [Nat.mul_assoc, ← Nat.add_assoc, ← Nat.mul_add, Nat.div_add_mod]
      have hlt : 2 ^ k0 * (a % 2 ^ d) + r < 2 ^ k0 * 2 ^ d := by
        have ham : a % 2 ^ d + 1 ≤ 2 ^ d := Nat.mod_lt a (Nat.two_pow_pos d)
        calc 2 ^ k0 * (a % 2 ^ d) + r < 2 ^ k0 * (a % 2 ^ d) + 2 ^ k0 := Nat.add_lt_add_left hr _
          _ = 2 ^ k0 * (a % 2 ^ d + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ ≤ 2 ^ k0 * 2 ^ d := Nat.mul_le_mul_left _ ham
      rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    have hb : (2 ^ k0 * b + r) % (2 ^ k0 * 2 ^ d) = 2 ^ k0 * (b % 2 ^ d) + r := by
      have h1 : 2 ^ k0 * b + r = (2 ^ k0 * 2 ^ d) * (b / 2 ^ d) + (2 ^ k0 * (b % 2 ^ d) + r) := by
        rw [Nat.mul_assoc, ← Nat.add_assoc, ← Nat.mul_add, Nat.div_add_mod]
      have hlt : 2 ^ k0 * (b % 2 ^ d) + r < 2 ^ k0 * 2 ^ d := by
        have hbm : b % 2 ^ d + 1 ≤ 2 ^ d := Nat.mod_lt b (Nat.two_pow_pos d)
        calc 2 ^ k0 * (b % 2 ^ d) + r < 2 ^ k0 * (b % 2 ^ d) + 2 ^ k0 := Nat.add_lt_add_left hr _
          _ = 2 ^ k0 * (b % 2 ^ d + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ ≤ 2 ^ k0 * 2 ^ d := Nat.mul_le_mul_left _ hbm
      rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    rw [hpow, ha, hb]
    constructor
    · intro heq
      have h1 : 2 ^ k0 * (a % 2 ^ d) = 2 ^ k0 * (b % 2 ^ d) := Nat.add_right_cancel heq
      exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos k0) h1
    · intro heq; rw [heq]
  refine ⟨Nat.mul_pos hbase.1 hR.1, ?_, ?_⟩
  · rw [Nat.mul_comm L M, returnMap_iter hf hL, hshift_eq]
    exact hR.2.1
  · intro t htpos htlt heq
    have hlo : iter f t r % 2 ^ k0 = r % 2 ^ k0 := by
      have h1 : iter f t (2 ^ k0 * q + r) % 2 ^ k0 = (2 ^ k0 * q + r) % 2 ^ k0 := by
        have hdvd : 2 ^ k0 ∣ 2 ^ (k0 + d) := by rw [Nat.pow_add]; exact Nat.dvd_mul_right _ _
        have := congrArg (· % 2 ^ k0) heq
        simpa [Nat.mod_mod_of_dvd _ hdvd] using this
      have hqr : (2 ^ k0 * q + r) % 2 ^ k0 = r % 2 ^ k0 := Nat.mul_add_mod _ _ _
      rw [causal_iter hf k0 t _ _ hqr, hqr] at h1
      exact h1
    rcases causal_period_dvd hf hbase hlo with ⟨m, rfl⟩
    have hmpos : 0 < m := by
      cases m with
      | zero => simp at htpos
      | succ _ => omega
    have hmlt : m < M := by
      rcases Nat.lt_or_ge m M with hlt | hge
      · exact hlt
      · exfalso
        have : L * M ≤ L * m := Nat.mul_le_mul_left L hge
        omega
    rw [Nat.mul_comm L m, returnMap_iter hf hL, hshift_eq] at heq
    exact hR.2.2 m hmpos hmlt heq

-- ============================================================================
-- PART V-A: UNIVERSAL RIPPLE-CARRY LEMMA & THEOREMS 1, 1b
--           (PROVED VIA ENGINE 2: F_2 CARRY-TRANSDUCER EIGENCYCLE COMPILER)
-- ============================================================================

/-- Hardware ripple-carry bit at position `k` for `u + v + c0` (with `c0 ≤ 1`). -/
def rCarry (u v c0 k : Nat) : Nat :=
  (u % 2 ^ k + v % 2 ^ k + c0) / 2 ^ k

theorem rCarry_zero (u v c0 : Nat) : rCarry u v c0 0 = c0 := by
  simp [rCarry, Nat.mod_one]

theorem rCarry_le_one (u v c0 k : Nat) (hc0 : c0 ≤ 1) : rCarry u v c0 k ≤ 1 := by
  unfold rCarry
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hu : u % 2 ^ k < 2 ^ k := Nat.mod_lt u hpos
  have hv : v % 2 ^ k < 2 ^ k := Nat.mod_lt v hpos
  have hlt : u % 2 ^ k + v % 2 ^ k + c0 < 2 ^ k * 2 := by omega
  have hle : (u % 2 ^ k + v % 2 ^ k + c0) / 2 ^ k < 2 := by
    exact (Nat.div_lt_iff_lt_mul hpos).mpr (by rw [Nat.mul_comm]; exact hlt)
  omega

theorem mod_two_pow_succ_eq (a k : Nat) :
    a % 2 ^ (k + 1) = a % 2 ^ k + (if a.testBit k then 1 else 0) * 2 ^ k := by
  have hdiv : a % 2 ^ (k + 1) / 2 ^ k = (a / 2 ^ k) % 2 := by
    rw [Nat.pow_succ, Nat.mod_mul_right_div_self]
  have hmod : a % 2 ^ (k + 1) % 2 ^ k = a % 2 ^ k :=
    Nat.mod_mod_of_dvd a (by rw [Nat.pow_succ]; exact Nat.dvd_mul_right _ _)
  have hdm : 2 ^ k * (a % 2 ^ (k + 1) / 2 ^ k) + a % 2 ^ (k + 1) % 2 ^ k = a % 2 ^ (k + 1) :=
    Nat.div_add_mod _ _
  rw [hdiv, hmod] at hdm
  rw [testBit_eq_div_mod]
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ k) with h0 | h1
  · rw [h0] at hdm ⊢; simp; omega
  · rw [h1] at hdm ⊢; simp; omega

theorem rCarry_succ (u v c0 k : Nat) :
    rCarry u v c0 (k + 1) =
    ((if u.testBit k then 1 else 0) + (if v.testBit k then 1 else 0) + rCarry u v c0 k) / 2 := by
  unfold rCarry
  rw [mod_two_pow_succ_eq u k, mod_two_pow_succ_eq v k, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hre : u % 2 ^ k + (if u.testBit k then 1 else 0) * 2 ^ k +
             (v % 2 ^ k + (if v.testBit k then 1 else 0) * 2 ^ k) + c0 =
             (u % 2 ^ k + v % 2 ^ k + c0) +
             ((if u.testBit k then 1 else 0) + (if v.testBit k then 1 else 0)) * 2 ^ k := by
    rw [Nat.add_mul]; omega
  rw [hre, Nat.add_mul_div_right _ _ hpos]
  omega

theorem testBit_add_add_ripple (u v c0 k : Nat) (hc0 : c0 ≤ 1) :
    (u + v + c0).testBit k = xor (u.testBit k) (xor (v.testBit k) (rCarry u v c0 k == 1)) := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hu : u = 2 ^ k * (u / 2 ^ k) + u % 2 ^ k := (Nat.div_add_mod u (2 ^ k)).symm
  have hv : v = 2 ^ k * (v / 2 ^ k) + v % 2 ^ k := (Nat.div_add_mod v (2 ^ k)).symm
  have hsum : u + v + c0 = 2 ^ k * (u / 2 ^ k + v / 2 ^ k) + (u % 2 ^ k + v % 2 ^ k + c0) := by
    rw [Nat.mul_add]; omega
  have hdiv : (u + v + c0) / 2 ^ k = u / 2 ^ k + v / 2 ^ k + rCarry u v c0 k := by
    rw [hsum, Nat.mul_add_div hpos]; rfl
  rw [testBit_eq_div_mod, testBit_eq_div_mod, testBit_eq_div_mod, hdiv]
  have hrc : rCarry u v c0 k ≤ 1 := rCarry_le_one u v c0 k hc0
  have hmod : (u / 2 ^ k + v / 2 ^ k + rCarry u v c0 k) % 2 =
              ((u / 2 ^ k) % 2 + (v / 2 ^ k) % 2 + rCarry u v c0 k) % 2 := by omega
  rw [hmod]
  rcases Nat.mod_two_eq_zero_or_one (u / 2 ^ k) with h1 | h1 <;>
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ k) with h2 | h2 <;>
  rcases (show rCarry u v c0 k = 0 ∨ rCarry u v c0 k = 1 by omega) with h3 | h3 <;>
  simp [h1, h2, h3]

/-- Helper: bit `k` of `2^a * (x &&& (x <<< b))`. -/
theorem testBit_pow2_mul_and_shift (a b x k : Nat) :
    (2 ^ a * (x &&& (x <<< b))).testBit k =
    if a + b ≤ k then x.testBit (k - a) && x.testBit (k - a - b) else false := by
  have h1 : 2 ^ a * (x &&& (x <<< b)) = (x &&& (x <<< b)) <<< a := by
    rw [Nat.shiftLeft_eq (x &&& (x <<< b)) a, Nat.mul_comm]
  rw [h1, Nat.testBit_shiftLeft]
  by_cases ha : a ≤ k
  · simp only [ha, Nat.testBit_and, Nat.testBit_shiftLeft, decide_true, Bool.true_and]
    by_cases hab : a + b ≤ k
    · have hb : b ≤ k - a := by omega
      simp [hab, hb]
    · have hb : ¬(b ≤ k - a) := by omega
      simp [hab, hb]
  · have hab : ¬(a + b ≤ k) := by omega
    simp [ha, hab]

theorem testBit_two_mul_or_shift (x k : Nat) :
    (2 * (x ||| (x <<< 1))).testBit k =
    if 1 ≤ k then x.testBit (k - 1) || (if 2 ≤ k then x.testBit (k - 2) else false) else false := by
  have h1 : 2 * (x ||| (x <<< 1)) = (x ||| (x <<< 1)) <<< 1 := by
    rw [Nat.shiftLeft_eq (x ||| (x <<< 1)) 1, Nat.pow_one, Nat.mul_comm]
  rw [h1, Nat.testBit_shiftLeft]
  by_cases h1k : 1 ≤ k
  · simp only [h1k, Nat.testBit_or, Nat.testBit_shiftLeft, decide_true, Bool.true_and]
    by_cases h2k : 2 ≤ k
    · have hb : 1 ≤ k - 1 := by omega
      have hsub : k - 1 - 1 = k - 2 := by omega
      simp [h2k, hb, hsub]
    · have hb : ¬(1 ≤ k - 1) := by omega
      simp [h2k, hb]
  · simp [h1k]

/-- Helper: shifted history bit `x.testBit (k - s)` encoded as `Nat` (0 or 1). -/
def b2n (b : Bool) : Nat := if b then 1 else 0

theorem b2n_le_one (b : Bool) : b2n b ≤ 1 := by
  cases b <;> decide

-- ----------------------------------------------------------------------------
-- THEOREM 1: EXACT 2-CYCLE SPLITTING & PERIOD-DOUBLING OF H111
--   H111(x) = x + 2 * (x &&& (x <<< 1)) + 1
--   - w = 1, 2 : De Bruijn single cycle of length 2^w
--   - w >= 3   : EXACTLY TWO DISJOINT CYCLES of exact minimal period 2^(w - 1)
--                (sector x_2 = 0 and sector x_2 = 1), certified by a 3-cycle
--                in the 8-state F_2 Carry-Transducer!
-- ----------------------------------------------------------------------------

def T_H111 : CarryTransducer 8 where
  init := 1
  next s xk :=
    let a := (s / 4) % 2
    let b := (s / 2) % 2
    let c := s % 2
    let xkn := b2n xk
    let cout := (xkn + (a &&& b) + c) / 2
    xkn * 4 + a * 2 + cout
  toggle s :=
    let a := (s / 4) % 2
    let b := (s / 2) % 2
    let c := s % 2
    ((a &&& b) ^^^ c) == 1

theorem T_H111_valid : T_H111.Valid := ⟨by decide, by decide⟩

theorem runTransducer_H111 (w x : Nat) :
    runTransducer T_H111 w x =
      b2n (if 1 ≤ w then x.testBit (w - 1) else false) * 4 +
      b2n (if 2 ≤ w then x.testBit (w - 2) else false) * 2 +
      rCarry x (2 * (x &&& (x <<< 1))) 1 w := by
  induction w with
  | zero => simp [runTransducer, T_H111, rCarry_zero, b2n]
  | succ w ih =>
    simp only [runTransducer, ih]
    let a := b2n (if 1 ≤ w then x.testBit (w - 1) else false)
    let b := b2n (if 2 ≤ w then x.testBit (w - 2) else false)
    let c := rCarry x (2 * (x &&& (x <<< 1))) 1 w
    change T_H111.next (a * 4 + b * 2 + c) (x.testBit w) = _
    have ha : a ≤ 1 := b2n_le_one _
    have hb : b ≤ 1 := b2n_le_one _
    have hc : c ≤ 1 := rCarry_le_one _ _ 1 w (Nat.le_refl 1)
    have hdiv4 : (a * 4 + b * 2 + c) / 4 % 2 = a := by omega
    have hdiv2 : (a * 4 + b * 2 + c) / 2 % 2 = b := by omega
    have hmod2 : (a * 4 + b * 2 + c) % 2 = c := by omega
    have hab_eq : (a &&& b) = b2n ((2 * (x &&& (x <<< 1))).testBit w) := by
      have htb := testBit_pow2_mul_and_shift 1 1 x w
      simp only [Nat.pow_one] at htb
      rw [htb]
      by_cases h2 : 2 ≤ w
      · have h1 : 1 ≤ w := by omega
        have hsub : w - 1 - 1 = w - 2 := by omega
        simp only [a, b, h1, h2, hsub, ↓reduceIte, b2n]
        cases x.testBit (w - 1) <;> cases x.testBit (w - 2) <;> rfl
      · simp only [a, b, h2, ↓reduceIte, b2n]
        cases (if 1 ≤ w then x.testBit (w - 1) else false) <;> rfl
    have hrc : rCarry x (2 * (x &&& (x <<< 1))) 1 (w + 1) =
               (b2n (x.testBit w) + (a &&& b) + c) / 2 := by
      rw [rCarry_succ, hab_eq]; rfl
    have hw1 : 1 ≤ w + 1 := by omega
    have hsub1 : w + 1 - 1 = w := by omega
    have hw2 : (if 2 ≤ w + 1 then x.testBit (w + 1 - 2) else false) =
               (if 1 ≤ w then x.testBit (w - 1) else false) := by
      by_cases h1 : 1 ≤ w
      · have h2 : 2 ≤ w + 1 := by omega
        have hs : w + 1 - 2 = w - 1 := by omega
        simp [h1, h2, hs]
      · have h2 : ¬(2 ≤ w + 1) := by omega
        simp [h1, h2]
    simp only [T_H111, hdiv4, hdiv2, hmod2, hw1, hsub1, hw2, ↓reduceIte, hrc]; rfl

theorem H111_bitSliced :
    BitSlicedInvertible H111 (fun w y => T_H111.toggle (runTransducer T_H111 w y)) := by
  have hbit : ∀ w x, (H111 x).testBit w = xor (x.testBit w) (T_H111.toggle (runTransducer T_H111 w x)) := by
    intro w x
    unfold H111
    rw [testBit_add_add_ripple _ _ 1 w (Nat.le_refl 1), runTransducer_H111]
    let a := b2n (if 1 ≤ w then x.testBit (w - 1) else false)
    let b := b2n (if 2 ≤ w then x.testBit (w - 2) else false)
    let c := rCarry x (2 * (x &&& (x <<< 1))) 1 w
    change (x.testBit w ^^ ((2 * (x &&& x <<< 1)).testBit w ^^ (c == 1))) =
           (x.testBit w ^^ T_H111.toggle (a * 4 + b * 2 + c))
    have ha : a ≤ 1 := b2n_le_one _
    have hb : b ≤ 1 := b2n_le_one _
    have hc : c ≤ 1 := rCarry_le_one _ _ 1 w (Nat.le_refl 1)
    have hdiv4 : (a * 4 + b * 2 + c) / 4 % 2 = a := by omega
    have hdiv2 : (a * 4 + b * 2 + c) / 2 % 2 = b := by omega
    have hmod2 : (a * 4 + b * 2 + c) % 2 = c := by omega
    have hab_eq : (a &&& b) = b2n ((2 * (x &&& (x <<< 1))).testBit w) := by
      have htb := testBit_pow2_mul_and_shift 1 1 x w
      simp only [Nat.pow_one] at htb
      rw [htb]
      by_cases h2 : 2 ≤ w
      · have h1 : 1 ≤ w := by omega
        have hsub : w - 1 - 1 = w - 2 := by omega
        simp only [a, b, h1, h2, hsub, ↓reduceIte, b2n]
        cases x.testBit (w - 1) <;> cases x.testBit (w - 2) <;> rfl
      · simp only [a, b, h2, ↓reduceIte, b2n]
        cases (if 1 ≤ w then x.testBit (w - 1) else false) <;> rfl
    simp only [T_H111, hdiv4, hdiv2, hmod2, hab_eq]
    congr 1
    cases (2 * (x &&& (x <<< 1))).testBit w <;>
    rcases (show c = 0 ∨ c = 1 by omega) with hc0 | hc1 <;>
    simp [b2n, *]
  refine ⟨?_, ?_⟩
  · intro w x y hxy
    rw [mod_two_pow_eq_iff] at hxy ⊢
    intro i hi
    rw [hbit i x, hbit i y, hxy i hi]
    have hmod_i : x % 2 ^ i = y % 2 ^ i := (mod_two_pow_eq_iff i x y).mpr (fun j hj => hxy j (Nat.lt_trans hj hi))
    rw [← runTransducer_mod T_H111 i x, ← runTransducer_mod T_H111 i y, hmod_i]
  · intro w x
    rw [hbit w x]; dsimp only; rw [runTransducer_mod T_H111 w x]

/-- Decidable ExactPeriod check for small base widths `w0`! -/
def checkExactPeriod (f : Nat → Nat) (w x L : Nat) : Bool :=
  (0 < L) &&
  (iter f L x % 2 ^ w == x % 2 ^ w) &&
  (List.range L).all (fun t => (t == 0) || (iter f t x % 2 ^ w != x % 2 ^ w))

theorem exactPeriod_of_check {f : Nat → Nat} {w x L : Nat}
    (h : checkExactPeriod f w x L = true) : ExactPeriod f w x L := by
  simp only [checkExactPeriod, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with ⟨⟨hLpos, hLper⟩, hall⟩
  refine ⟨hLpos, hLper, ?_⟩
  intro t htpos htlt
  have ht := List.all_eq_true.mp hall t (List.mem_range.mpr htlt)
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at ht
  rcases ht with rfl | hne
  · omega
  · exact hne

/-- Synthesized F_2 3-cycle certificates for Theorem 1 (`H111`). -/
def cert_H111_sector0 : LassoCert := { pre := [], cyc := [12, 48, 192] }

def cert_H111_sector1 : LassoCert := { pre := [], cyc := [192, 12, 48] }

/-- THEOREM 1 (Exact 2-Cycle Splitting & Period-Doubling for Additive Carry-AND NLFSR H111):
    For `H111(x) = x + 2 * (x &&& (x <<< 1)) + 1`:
    1. At `w = 1, 2`: De Bruijn complete (single cycle of length `2^w`).
    2. At EVERY `w ≥ 3`: the state space `0 .. 2^w - 1` partitions into EXACTLY TWO
       disjoint invariant cycles of exact minimal period `2^(w - 1)`:
         - Sector 0 (`x.testBit 2 = false`): single cycle of exact length `2^(w - 1)`
         - Sector 1 (`x.testBit 2 = true`) : single cycle of exact length `2^(w - 1)` -/
theorem theorem1_H111_debruijn_base :
    SingleCycle H111 1 ∧ SingleCycle H111 2 := by
  exact ⟨singleCycle_of_zero H111_bitSliced.1 (exactPeriod_of_check (by decide)),
         singleCycle_of_zero H111_bitSliced.1 (exactPeriod_of_check (by decide))⟩

theorem theorem1_H111_exact_two_cycles (w : Nat) (hw : w ≥ 3) :
    (∀ x, x.testBit 2 = false → ExactPeriod H111 w x (2 ^ (w - 1))) ∧
    (∀ x, x.testBit 2 = true  → ExactPeriod H111 w x (2 ^ (w - 1))) ∧
    (∀ x y t, x.testBit 2 = false → y.testBit 2 = true → iter H111 t x % 2 ^ w ≠ y % 2 ^ w) := by
  let P0 : Nat → Bool := fun y => !y.testBit 2
  let P1 : Nat → Bool := fun y => y.testBit 2
  have hP0_inv : ∀ y, P0 (y % 2 ^ 3) = true → P0 (H111 y % 2 ^ 3) = true := by
    intro y hy
    rw [← causal_mod H111_bitSliced.1 3 y]
    have hlt : y % 8 < 8 := Nat.mod_lt y (by omega)
    have hfin : ∀ r < 8, P0 r = true → P0 (H111 r % 8) = true := by decide
    exact hfin (y % 8) hlt hy
  have hP1_inv : ∀ y, P1 (y % 2 ^ 3) = true → P1 (H111 y % 2 ^ 3) = true := by
    intro y hy
    rw [← causal_mod H111_bitSliced.1 3 y]
    have hlt : y % 8 < 8 := Nat.mod_lt y (by omega)
    have hfin : ∀ r < 8, P1 r = true → P1 (H111 r % 8) = true := by decide
    exact hfin (y % 8) hlt hy
  have hsec0 : ∀ d, ExactPeriod H111 (3 + d) 0 (4 * 2 ^ d) :=
    transducer_cert_period_doubling H111_bitSliced T_H111 T_H111_valid P0 3 4 0
      (fun _ _ _ _ => rfl) hP0_inv (by decide) (by decide)
      (exactPeriod_of_check (by decide)) cert_H111_sector0 (by decide)
  have hsec1 : ∀ d, ExactPeriod H111 (3 + d) 4 (4 * 2 ^ d) :=
    transducer_cert_period_doubling H111_bitSliced T_H111 T_H111_valid P1 3 4 4
      (fun _ _ _ _ => rfl) hP1_inv (by decide) (by decide)
      (exactPeriod_of_check (by decide)) cert_H111_sector1 (by decide)
  let d := w - 3
  have hw_eq : 3 + d = w := by omega
  have hpow_eq : 4 * 2 ^ d = 2 ^ (w - 1) := by
    have : w - 1 = 2 + d := by omega
    rw [this, Nat.pow_add]
  have hbit2_mod : ∀ z, (z % 8).testBit 2 = z.testBit 2 := by
    intro z; rw [show (8 : Nat) = 2 ^ 3 by rfl, Nat.testBit_mod_two_pow]; simp
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have h0 := exactPeriod_of_cylinder_mem H111_bitSliced.1 (y := x) hP0_inv (by decide) (by decide)
      (by simp [P0, hbit2_mod, hx]) (hsec0 d)
    rwa [hw_eq, hpow_eq] at h0
  · intro x hx
    have h1 := exactPeriod_of_cylinder_mem H111_bitSliced.1 (y := x) hP1_inv (by decide) (by decide)
      (by simp [P1, hbit2_mod, hx]) (hsec1 d)
    rwa [hw_eq, hpow_eq] at h1
  · intro x y t hx hy heq
    have horb0 : ∀ m, P0 (iter H111 m x % 2 ^ 3) = true := by
      intro m; induction m with
      | zero => simp [iter, P0, hbit2_mod, hx]
      | succ m ih => exact hP0_inv _ ih
    have hmod3 : iter H111 t x % 2 ^ 3 = y % 2 ^ 3 := by
      have hdvd : 2 ^ 3 ∣ 2 ^ w := Nat.pow_dvd_pow 2 hw
      have := congrArg (· % 2 ^ 3) heq
      simpa [Nat.mod_mod_of_dvd _ hdvd] using this
    have ht0 := horb0 t
    rw [hmod3] at ht0
    simp [P0, hbit2_mod, hy] at ht0

-- ----------------------------------------------------------------------------
-- THEOREM 1b: UNIVERSAL DE BRUIJN COMPLETENESS FOR ADDITIVE HYBRID NLFSRs
--   (i)   K_map(x) = (x ^^^ (x <<< 1)) + 2 * (x ||| (x <<< 1)) + 1  (8-state fixed point!)
--   (ii)  H121(x)  = x + 2 * (x &&& (x <<< 2)) + 1                  (16-state 2-cycle!)
--   (iii) H211(x)  = x + 4 * (x &&& (x <<< 1)) + 1                  (16-state 5-cycle!)
-- ----------------------------------------------------------------------------

def K_map (x : Nat) : Nat := (x ^^^ (x <<< 1)) + 2 * (x ||| (x <<< 1)) + 1

def T_K : CarryTransducer 8 where
  init := 1
  next s xk :=
    let a := (s / 4) % 2
    let b := (s / 2) % 2
    let c := s % 2
    let xkn := b2n xk
    let cout := ((xkn ^^^ a) + (a ||| b) + c) / 2
    xkn * 4 + a * 2 + cout
  toggle s :=
    let a := (s / 4) % 2
    let b := (s / 2) % 2
    let c := s % 2
    ((a ^^^ (a ||| b)) ^^^ c) == 1

theorem T_K_valid : T_K.Valid := ⟨by decide, by decide⟩

theorem runTransducer_K (w x : Nat) :
    runTransducer T_K w x =
      b2n (if 1 ≤ w then x.testBit (w - 1) else false) * 4 +
      b2n (if 2 ≤ w then x.testBit (w - 2) else false) * 2 +
      rCarry (x ^^^ (x <<< 1)) (2 * (x ||| (x <<< 1))) 1 w := by
  induction w with
  | zero => simp [runTransducer, T_K, rCarry_zero, b2n]
  | succ w ih =>
    simp only [runTransducer, ih]
    let a := b2n (if 1 ≤ w then x.testBit (w - 1) else false)
    let b := b2n (if 2 ≤ w then x.testBit (w - 2) else false)
    let c := rCarry (x ^^^ (x <<< 1)) (2 * (x ||| (x <<< 1))) 1 w
    change T_K.next (a * 4 + b * 2 + c) (x.testBit w) = _
    have ha : a ≤ 1 := b2n_le_one _
    have hb : b ≤ 1 := b2n_le_one _
    have hc : c ≤ 1 := rCarry_le_one _ _ 1 w (Nat.le_refl 1)
    have hdiv4 : (a * 4 + b * 2 + c) / 4 % 2 = a := by omega
    have hdiv2 : (a * 4 + b * 2 + c) / 2 % 2 = b := by omega
    have hmod2 : (a * 4 + b * 2 + c) % 2 = c := by omega
    have hu_eq : (b2n (x.testBit w) ^^^ a) = b2n ((x ^^^ (x <<< 1)).testBit w) := by
      rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
      by_cases h1 : 1 ≤ w
      · simp only [a, h1, decide_true, Bool.true_and, ↓reduceIte, b2n]
        cases x.testBit w <;> cases x.testBit (w - 1) <;> rfl
      · simp only [a, h1, decide_false, Bool.false_and, ↓reduceIte, b2n]
        cases x.testBit w <;> rfl
    have hv_eq : (a ||| b) = b2n ((2 * (x ||| (x <<< 1))).testBit w) := by
      rw [testBit_two_mul_or_shift]
      by_cases h1 : 1 ≤ w
      · by_cases h2 : 2 ≤ w
        · simp only [a, b, h1, h2, ↓reduceIte, b2n]
          cases x.testBit (w - 1) <;> cases x.testBit (w - 2) <;> rfl
        · simp only [a, b, h1, h2, ↓reduceIte, b2n]
          cases x.testBit (w - 1) <;> rfl
      · have h2 : ¬(2 ≤ w) := by omega
        simp only [a, b, h1, h2, ↓reduceIte, b2n]; rfl
    have hrc : rCarry (x ^^^ (x <<< 1)) (2 * (x ||| (x <<< 1))) 1 (w + 1) =
               ((b2n (x.testBit w) ^^^ a) + (a ||| b) + c) / 2 := by
      rw [rCarry_succ, hu_eq, hv_eq]; rfl
    have hw1 : 1 ≤ w + 1 := by omega
    have hsub1 : w + 1 - 1 = w := by omega
    have hw2 : (if 2 ≤ w + 1 then x.testBit (w + 1 - 2) else false) =
               (if 1 ≤ w then x.testBit (w - 1) else false) := by
      by_cases h1 : 1 ≤ w
      · have h2 : 2 ≤ w + 1 := by omega
        have hs : w + 1 - 2 = w - 1 := by omega
        simp [h1, h2, hs]
      · have h2 : ¬(2 ≤ w + 1) := by omega
        simp [h1, h2]
    simp only [T_K, hdiv4, hdiv2, hmod2, hw1, hsub1, hw2, ↓reduceIte, hrc]; rfl

theorem K_map_bitSliced :
    BitSlicedInvertible K_map (fun w y => T_K.toggle (runTransducer T_K w y)) := by
  have hbit : ∀ w x, (K_map x).testBit w = xor (x.testBit w) (T_K.toggle (runTransducer T_K w x)) := by
    intro w x
    unfold K_map
    rw [testBit_add_add_ripple _ _ 1 w (Nat.le_refl 1), runTransducer_K]
    let a := b2n (if 1 ≤ w then x.testBit (w - 1) else false)
    let b := b2n (if 2 ≤ w then x.testBit (w - 2) else false)
    let c := rCarry (x ^^^ (x <<< 1)) (2 * (x ||| (x <<< 1))) 1 w
    change ((x ^^^ x <<< 1).testBit w ^^ ((2 * (x ||| x <<< 1)).testBit w ^^ (c == 1))) =
           (x.testBit w ^^ T_K.toggle (a * 4 + b * 2 + c))
    have ha : a ≤ 1 := b2n_le_one _
    have hb : b ≤ 1 := b2n_le_one _
    have hc : c ≤ 1 := rCarry_le_one _ _ 1 w (Nat.le_refl 1)
    have hdiv4 : (a * 4 + b * 2 + c) / 4 % 2 = a := by omega
    have hdiv2 : (a * 4 + b * 2 + c) / 2 % 2 = b := by omega
    have hmod2 : (a * 4 + b * 2 + c) % 2 = c := by omega
    have hv_eq : (a ||| b) = b2n ((2 * (x ||| (x <<< 1))).testBit w) := by
      rw [testBit_two_mul_or_shift]
      by_cases h1 : 1 ≤ w
      · by_cases h2 : 2 ≤ w
        · simp only [a, b, h1, h2, ↓reduceIte, b2n]
          cases x.testBit (w - 1) <;> cases x.testBit (w - 2) <;> rfl
        · simp only [a, b, h1, h2, ↓reduceIte, b2n]
          cases x.testBit (w - 1) <;> rfl
      · have h2 : ¬(2 ≤ w) := by omega
        simp only [a, b, h1, h2, ↓reduceIte, b2n]; rfl
    have hu_bit : (x ^^^ (x <<< 1)).testBit w = xor (x.testBit w) (a == 1) := by
      rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
      by_cases h1 : 1 ≤ w
      · simp only [a, h1, decide_true, Bool.true_and, ↓reduceIte, b2n]
        cases x.testBit (w - 1) <;> rfl
      · simp only [a, h1, decide_false, Bool.false_and, ↓reduceIte, b2n]; rfl
    simp only [T_K, hdiv4, hdiv2, hmod2, hu_bit, bxor_assoc]
    congr 1
    rw [hv_eq]
    rcases (show a = 0 ∨ a = 1 by omega) with ha0 | ha1 <;>
    cases (2 * (x ||| (x <<< 1))).testBit w <;>
    rcases (show c = 0 ∨ c = 1 by omega) with hc0 | hc1 <;>
    simp [b2n, *]
  refine ⟨?_, ?_⟩
  · intro w x y hxy
    rw [mod_two_pow_eq_iff] at hxy ⊢
    intro i hi
    rw [hbit i x, hbit i y, hxy i hi]
    have hmod_i : x % 2 ^ i = y % 2 ^ i := (mod_two_pow_eq_iff i x y).mpr (fun j hj => hxy j (Nat.lt_trans hj hi))
    rw [← runTransducer_mod T_K i x, ← runTransducer_mod T_K i y, hmod_i]
  · intro w x
    rw [hbit w x]; dsimp only; rw [runTransducer_mod T_K w x]

def cert_K_debruijn : LassoCert := { pre := [33, 153, 243, 48], cyc := [192] }

/-- THEOREM 1b(i) (De Bruijn Completeness of Hybrid XOR-OR-Carry NLFSR `K_map`):
    `K_map(x) = (x ^^^ (x <<< 1)) + 2 * (x ||| (x <<< 1)) + 1` is De Bruijn complete
    (single cycle of length `2^w`) for ALL `w ≥ 1`, certified by an 8-state F_2 fixed-point lasso! -/
theorem theorem1b_K_map_debruijn (w : Nat) (hw : w ≥ 1) : SingleCycle K_map w := by
  have hall : ∀ d, ExactPeriod K_map (1 + d) 0 (2 * 2 ^ d) :=
    transducer_cert_period_doubling K_map_bitSliced T_K T_K_valid (fun _ => true) 1 2 0
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (by decide) rfl
      (exactPeriod_of_check (by decide)) cert_K_debruijn (by decide)
  have hd := hall (w - 1)
  have hw_eq : 1 + (w - 1) = w := by omega
  have hpow : 2 * 2 ^ (w - 1) = 2 ^ w := by
    conv => rhs; rw [show w = (w - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  rw [hw_eq, hpow] at hd
  exact singleCycle_of_zero K_map_bitSliced.1 hd

-- Also certify the 16-state additive Carry-AND De Bruijn NLFSR H121(x) = x + 2*(x &&& (x <<< 2)) + 1!

def T_H121 : CarryTransducer 16 where
  init := 1
  next s xk :=
    let a := (s / 8) % 2
    let b := (s / 4) % 2
    let d := (s / 2) % 2
    let c := s % 2
    let xkn := b2n xk
    let cout := (xkn + (a &&& d) + c) / 2
    xkn * 8 + a * 4 + b * 2 + cout
  toggle s :=
    let a := (s / 8) % 2
    let d := (s / 2) % 2
    let c := s % 2
    ((a &&& d) ^^^ c) == 1

theorem T_H121_valid : T_H121.Valid := ⟨by decide, by decide⟩

theorem runTransducer_H121 (w x : Nat) :
    runTransducer T_H121 w x =
      b2n (if 1 ≤ w then x.testBit (w - 1) else false) * 8 +
      b2n (if 2 ≤ w then x.testBit (w - 2) else false) * 4 +
      b2n (if 3 ≤ w then x.testBit (w - 3) else false) * 2 +
      rCarry x (2 * (x &&& (x <<< 2))) 1 w := by
  induction w with
  | zero => simp [runTransducer, T_H121, rCarry_zero, b2n]
  | succ w ih =>
    simp only [runTransducer, ih]
    let a := b2n (if 1 ≤ w then x.testBit (w - 1) else false)
    let b := b2n (if 2 ≤ w then x.testBit (w - 2) else false)
    let d := b2n (if 3 ≤ w then x.testBit (w - 3) else false)
    let c := rCarry x (2 * (x &&& (x <<< 2))) 1 w
    change T_H121.next (a * 8 + b * 4 + d * 2 + c) (x.testBit w) = _
    have ha : a ≤ 1 := b2n_le_one _
    have hb : b ≤ 1 := b2n_le_one _
    have hd : d ≤ 1 := b2n_le_one _
    have hc : c ≤ 1 := rCarry_le_one _ _ 1 w (Nat.le_refl 1)
    have hdiv8 : (a * 8 + b * 4 + d * 2 + c) / 8 % 2 = a := by omega
    have hdiv4 : (a * 8 + b * 4 + d * 2 + c) / 4 % 2 = b := by omega
    have hdiv2 : (a * 8 + b * 4 + d * 2 + c) / 2 % 2 = d := by omega
    have hmod2 : (a * 8 + b * 4 + d * 2 + c) % 2 = c := by omega
    have had_eq : (a &&& d) = b2n ((2 * (x &&& (x <<< 2))).testBit w) := by
      have htb := testBit_pow2_mul_and_shift 1 2 x w
      simp only [Nat.pow_one] at htb
      rw [htb]
      by_cases h3 : 3 ≤ w
      · have h1 : 1 ≤ w := by omega
        have hsub : w - 1 - 2 = w - 3 := by omega
        simp only [a, d, h1, h3, hsub, ↓reduceIte, b2n]
        cases x.testBit (w - 1) <;> cases x.testBit (w - 3) <;> rfl
      · simp only [a, d, h3, ↓reduceIte, b2n]
        cases (if 1 ≤ w then x.testBit (w - 1) else false) <;> rfl
    have hrc : rCarry x (2 * (x &&& (x <<< 2))) 1 (w + 1) =
               (b2n (x.testBit w) + (a &&& d) + c) / 2 := by
      rw [rCarry_succ, had_eq]; rfl
    have hw1 : 1 ≤ w + 1 := by omega
    have hsub1 : w + 1 - 1 = w := by omega
    have hw2 : (if 2 ≤ w + 1 then x.testBit (w + 1 - 2) else false) =
               (if 1 ≤ w then x.testBit (w - 1) else false) := by
      by_cases h1 : 1 ≤ w
      · have h2 : 2 ≤ w + 1 := by omega
        have hs : w + 1 - 2 = w - 1 := by omega
        simp [h1, h2, hs]
      · have h2 : ¬(2 ≤ w + 1) := by omega
        simp [h1, h2]
    have hw3 : (if 3 ≤ w + 1 then x.testBit (w + 1 - 3) else false) =
               (if 2 ≤ w then x.testBit (w - 2) else false) := by
      by_cases h2 : 2 ≤ w
      · have h3 : 3 ≤ w + 1 := by omega
        have hs : w + 1 - 3 = w - 2 := by omega
        simp [h2, h3, hs]
      · have h3 : ¬(3 ≤ w + 1) := by omega
        simp [h2, h3]
    simp only [T_H121, hdiv8, hdiv4, hdiv2, hmod2, hw1, hsub1, hw2, hw3, ↓reduceIte, hrc]; rfl

theorem H121_bitSliced :
    BitSlicedInvertible H121 (fun w y => T_H121.toggle (runTransducer T_H121 w y)) := by
  have hbit : ∀ w x, (H121 x).testBit w = xor (x.testBit w) (T_H121.toggle (runTransducer T_H121 w x)) := by
    intro w x
    unfold H121
    rw [testBit_add_add_ripple _ _ 1 w (Nat.le_refl 1), runTransducer_H121]
    let a := b2n (if 1 ≤ w then x.testBit (w - 1) else false)
    let b := b2n (if 2 ≤ w then x.testBit (w - 2) else false)
    let d := b2n (if 3 ≤ w then x.testBit (w - 3) else false)
    let c := rCarry x (2 * (x &&& (x <<< 2))) 1 w
    change (x.testBit w ^^ ((2 * (x &&& x <<< 2)).testBit w ^^ (c == 1))) =
           (x.testBit w ^^ T_H121.toggle (a * 8 + b * 4 + d * 2 + c))
    have ha : a ≤ 1 := b2n_le_one _
    have hb : b ≤ 1 := b2n_le_one _
    have hd : d ≤ 1 := b2n_le_one _
    have hc : c ≤ 1 := rCarry_le_one _ _ 1 w (Nat.le_refl 1)
    have hdiv8 : (a * 8 + b * 4 + d * 2 + c) / 8 % 2 = a := by omega
    have hdiv2 : (a * 8 + b * 4 + d * 2 + c) / 2 % 2 = d := by omega
    have hmod2 : (a * 8 + b * 4 + d * 2 + c) % 2 = c := by omega
    have had_eq : (a &&& d) = b2n ((2 * (x &&& (x <<< 2))).testBit w) := by
      have htb := testBit_pow2_mul_and_shift 1 2 x w
      simp only [Nat.pow_one] at htb
      rw [htb]
      by_cases h3 : 3 ≤ w
      · have h1 : 1 ≤ w := by omega
        have hsub : w - 1 - 2 = w - 3 := by omega
        simp only [a, d, h1, h3, hsub, ↓reduceIte, b2n]
        cases x.testBit (w - 1) <;> cases x.testBit (w - 3) <;> rfl
      · simp only [a, d, h3, ↓reduceIte, b2n]
        cases (if 1 ≤ w then x.testBit (w - 1) else false) <;> rfl
    simp only [T_H121, hdiv8, hdiv2, hmod2, had_eq]
    congr 1
    cases (2 * (x &&& (x <<< 2))).testBit w <;>
    rcases (show c = 0 ∨ c = 1 by omega) with hc0 | hc1 <;>
    simp [b2n, *]
  refine ⟨?_, ?_⟩
  · intro w x y hxy
    rw [mod_two_pow_eq_iff] at hxy ⊢
    intro i hi
    rw [hbit i x, hbit i y, hxy i hi]
    have hmod_i : x % 2 ^ i = y % 2 ^ i := (mod_two_pow_eq_iff i x y).mpr (fun j hj => hxy j (Nat.lt_trans hj hi))
    rw [← runTransducer_mod T_H121 i x, ← runTransducer_mod T_H121 i y, hmod_i]
  · intro w x
    rw [hbit w x]; dsimp only; rw [runTransducer_mod T_H121 w x]

def cert_H121_debruijn : LassoCert :=
  { pre := [513, 8465, 38229, 61632, 52416, 3312], cyc := [48, 3072] }

/-- THEOREM 1b(ii) (De Bruijn Completeness of Additive Carry-AND NLFSR `H121`):
    `H121(x) = x + 2 * (x &&& (x <<< 2)) + 1` is De Bruijn complete (single cycle of length `2^w`)
    for ALL `w ≥ 1`, certified by a 16-state F_2 period-2 eigencycle! -/
theorem theorem1b_H121_debruijn (w : Nat) (hw : w ≥ 1) : SingleCycle H121 w := by
  have hall : ∀ d, ExactPeriod H121 (1 + d) 0 (2 * 2 ^ d) :=
    transducer_cert_period_doubling H121_bitSliced T_H121 T_H121_valid (fun _ => true) 1 2 0
      (fun _ _ _ _ => rfl) (fun _ _ => rfl) (by decide) rfl
      (exactPeriod_of_check (by decide)) cert_H121_debruijn (by decide)
  have hd := hall (w - 1)
  have hw_eq : 1 + (w - 1) = w := by omega
  have hpow : 2 * 2 ^ (w - 1) = 2 ^ w := by
    conv => rhs; rw [show w = (w - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  rw [hw_eq, hpow] at hd
  exact singleCycle_of_zero H121_bitSliced.1 hd

-- ============================================================================
-- PART V-B: THEOREM 2 — UNIVERSAL CARRY-BARRIER & FROBENIUS CARRY-PUMP
--           BIFURCATION FOR ALL 2-DELAYED NONLINEAR FEEDBACKS N
-- ============================================================================

/-- Composition of two bit-sliced invertible maps is bit-sliced invertible. -/
theorem BitSlicedInvertible.comp {f g : Nat → Nat} {df dg : Nat → Nat → Bool}
    (hf : BitSlicedInvertible f df) (hg : BitSlicedInvertible g dg) :
    BitSlicedInvertible (fun x => g (f x)) (fun w y => xor (df w y) (dg w (f y % 2 ^ w))) := by
  refine ⟨?_, ?_⟩
  · intro w x y hxy
    exact hg.1 w _ _ (hf.1 w x y hxy)
  · intro w x
    rw [hg.2, hf.2, bxor_assoc]; dsimp only; rw [causal_mod hf.1]

theorem TwoDelayed.testBit_mod_eq {N : Nat → Nat} (hN : TwoDelayed N) {w x y : Nat}
    (hw : w ≥ 2) (hxy : x % 2 ^ (w - 1) = y % 2 ^ (w - 1)) :
    (N x).testBit w = (N y).testBit w := by
  rw [hN.2 w x hw, hN.2 w y hw, hxy]

theorem TwoDelayed.mod4_eq_zero {N : Nat → Nat} (hN : TwoDelayed N) (x : Nat) :
    N x % 4 = 0 := by
  rw [show (4 : Nat) = 2 ^ 2 by rfl]
  have h : N x % 2 ^ 2 = 0 % 2 ^ 2 := by
    rw [mod_two_pow_eq_iff]
    intro i hi
    have h0 : (0 : Nat).testBit i = false := Nat.zero_testBit i
    rw [h0]
    match i with
    | 0 => exact (hN.1 x).1
    | 1 => exact (hN.1 x).2
    | k + 2 => omega
  simpa using h

theorem TwoDelayed.causal {N : Nat → Nat} (hN : TwoDelayed N) : Causal N := by
  intro w x y hxy
  rw [mod_two_pow_eq_iff] at hxy ⊢
  intro i hi
  match i with
  | 0 => rw [(hN.1 x).1, (hN.1 y).1]
  | 1 => rw [(hN.1 x).2, (hN.1 y).2]
  | k + 2 =>
    apply hN.testBit_mod_eq (by omega)
    rw [mod_two_pow_eq_iff]
    intro j hj
    exact hxy j (by omega)

theorem hybridCarryNLFSR_causal {N : Nat → Nat} (hN : TwoDelayed N) (c : Nat) :
    Causal (hybridCarryNLFSR N c) := by
  intro w x y hxy
  unfold hybridCarryNLFSR
  have h1 : (x ^^^ (x <<< 1) ^^^ N x) % 2 ^ w = (y ^^^ (y <<< 1) ^^^ N y) % 2 ^ w := by
    rw [mod_two_pow_eq_iff] at hxy ⊢
    intro i hi
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft]
    have hNxy : (N x).testBit i = (N y).testBit i := by
      have hc := hN.causal w x y ((mod_two_pow_eq_iff w x y).mpr hxy)
      exact (mod_two_pow_eq_iff w _ _).mp hc i hi
    rw [hxy i hi, hNxy]
    by_cases h1i : 1 ≤ i
    · simp [h1i, hxy (i - 1) (by omega)]
    · simp [h1i]
  have hmod : ∀ a, (a + c) % 2 ^ w = (a % 2 ^ w + c % 2 ^ w) % 2 ^ w := fun a => Nat.add_mod a c _
  rw [hmod, hmod, h1]

/-- Helper: bit `k` of `(a / 4)` is `a.testBit (k + 2)`. -/
theorem testBit_div_four (a k : Nat) : (a / 4).testBit k = a.testBit (k + 2) := by
  have h : a / 4 = a >>> 2 := by rw [Nat.shiftRight_eq_div_pow]
  rw [h, Nat.testBit_shiftRight, Nat.add_comm]

theorem testBit_four_mul (q k : Nat) :
    (4 * q).testBit k = if 2 ≤ k then q.testBit (k - 2) else false := by
  have h : 4 * q = q <<< 2 := by rw [Nat.shiftLeft_eq, Nat.mul_comm]
  rw [h, Nat.testBit_shiftLeft]
  by_cases h2 : 2 ≤ k <;> simp [h2]

theorem testBit_four_mul_add_one (q k : Nat) :
    (4 * q + 1).testBit k = if k = 0 then true else if 2 ≤ k then q.testBit (k - 2) else false := by
  have h : 4 * q + 1 = (4 * q) ||| 1 := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_or, testBit_four_mul]
    match i with
    | 0 =>
      rw [testBit_eq_div_mod]
      have : (4 * q + 1) % 2 = 1 := by omega
      simp [this]
    | 1 =>
      rw [testBit_eq_div_mod]
      have : (4 * q + 1) / 2 ^ 1 % 2 = 0 := by omega
      have h11 : (1 : Nat).testBit 1 = false := by decide
      simp [this, h11]
    | m + 2 =>
      rw [testBit_eq_div_mod]
      have hdiv : (4 * q + 1) / 2 ^ (m + 2) = q / 2 ^ m := by
        rw [Nat.pow_add, show 2 ^ 2 = 4 by rfl, Nat.mul_comm (2 ^ m) 4, ← Nat.div_div_eq_div_mul]
        have : (4 * q + 1) / 4 = q := by omega
        rw [this]
      rw [hdiv, ← testBit_eq_div_mod]
      have h1 : (1 : Nat).testBit (m + 2) = false := by
        rw [testBit_eq_div_mod]
        have : 1 / 2 ^ (m + 2) = 0 := Nat.div_eq_of_lt (by have := Nat.two_pow_pos m; rw [Nat.pow_add]; omega)
        simp [this]
      simp [h1]
  rw [h, Nat.testBit_or, testBit_four_mul]
  match k with
  | 0 => rfl
  | 1 => rfl
  | m + 2 =>
    have h1 : (1 : Nat).testBit (m + 2) = false := by
      rw [testBit_eq_div_mod]
      have : 1 / 2 ^ (m + 2) = 0 := Nat.div_eq_of_lt (by have := Nat.two_pow_pos m; rw [Nat.pow_add]; omega)
      simp [this]
    simp [h1]

/-- THEOREM 2b (Universal Hermetic Carry-Barrier Collapse on `x.testBit 1 = true`):
    For EVERY 2-delayed nonlinear feedback `N` and EVERY `x` with `x.testBit 1 = true`:
    1. `(hybridCarryNLFSR N 1 x).testBit 1 = true` (sector invariance), AND
    2. `(hybridCarryNLFSR N 1 x) / 4 = (x ^^^ (x <<< 1) ^^^ N x) / 4` (ZERO carry crosses bit 1!). -/
theorem theorem2b_carry_barrier_hermetic {N : Nat → Nat} (hN : TwoDelayed N) (x : Nat)
    (hx : x.testBit 1 = true) :
    (hybridCarryNLFSR N 1 x).testBit 1 = true ∧
    hybridCarryNLFSR N 1 x / 4 = (x ^^^ (x <<< 1) ^^^ N x) / 4 := by
  unfold hybridCarryNLFSR
  let u := x ^^^ (x <<< 1) ^^^ N x
  have hu0 : u.testBit 0 = x.testBit 0 := by
    dsimp only [u]
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, (hN.1 x).1]
    simp
  have hu1 : u.testBit 1 = !(x.testBit 0) := by
    dsimp only [u]
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, hx, (hN.1 x).2]
    cases x.testBit 0 <;> rfl
  have hu_mod4 : u % 4 = if x.testBit 0 then 1 else 2 := by
    have hlt : u % 4 < 4 := Nat.mod_lt u (by omega)
    have hb0 : (u % 4).testBit 0 = u.testBit 0 := by
      rw [show (4 : Nat) = 2 ^ 2 by rfl, Nat.testBit_mod_two_pow]; simp
    have hb1 : (u % 4).testBit 1 = u.testBit 1 := by
      rw [show (4 : Nat) = 2 ^ 2 by rfl, Nat.testBit_mod_two_pow]; simp
    cases hx0 : x.testBit 0
    · rw [hx0] at hu0 hu1; rw [hu0] at hb0; rw [hu1] at hb1; simp only [Bool.false_eq_true, ↓reduceIte]
      have hcases : u % 4 = 0 ∨ u % 4 = 1 ∨ u % 4 = 2 ∨ u % 4 = 3 := by omega
      rcases hcases with h | h | h | h
      · rw [h] at hb0 hb1; exact absurd hb1 (by decide)
      · rw [h] at hb0 hb1; exact absurd hb0 (by decide)
      · exact h
      · rw [h] at hb0 hb1; exact absurd hb0 (by decide)
    · rw [hx0] at hu0 hu1; rw [hu0] at hb0; rw [hu1] at hb1; simp only [↓reduceIte]
      have hcases : u % 4 = 0 ∨ u % 4 = 1 ∨ u % 4 = 2 ∨ u % 4 = 3 := by omega
      rcases hcases with h | h | h | h
      · rw [h] at hb0 hb1; exact absurd hb0 (by decide)
      · exact h
      · rw [h] at hb0 hb1; exact absurd hb0 (by decide)
      · rw [h] at hb0 hb1; exact absurd hb1 (by decide)
  have hu_eq : u = 4 * (u / 4) + u % 4 := (Nat.div_add_mod u 4).symm
  cases hx0 : x.testBit 0 <;> rw [hx0] at hu_mod4 <;> simp at hu_mod4
  · -- u % 4 = 2, so u + 1 = 4*(u/4) + 3
    have h1 : (u + 1) / 4 = u / 4 := by omega
    have h2 : (u + 1) / 2 % 2 = 1 := by omega
    exact ⟨by rw [testBit_eq_div_mod, Nat.pow_one, h2]; rfl, h1⟩
  · -- u % 4 = 1, so u + 1 = 4*(u/4) + 2
    have h1 : (u + 1) / 4 = u / 4 := by omega
    have h2 : (u + 1) / 2 % 2 = 1 := by omega
    exact ⟨by rw [testBit_eq_div_mod, Nat.pow_one, h2]; rfl, h1⟩

/-- THEOREM 2a (Universal Frobenius Carry-Pump Giant Cycle):
    For EVERY 2-delayed nonlinear feedback `N` satisfying the finite-slice parity gate
    `(N 0).testBit 2 = (N 1).testBit 2`, EVERY `c` with `c % 4 = 1`, EVERY `w ≥ 2`,
    and EVERY `x` in the Carry-Pump Sector (`x.testBit 1 = false`):
      `ExactPeriod (hybridCarryNLFSR N c) w x (2 ^ (w - 1))`! -/
theorem theorem2a_carry_pump_universal_giant_cycle
    {N : Nat → Nat} (hN : TwoDelayed N)
    (hgate : (N 0).testBit 2 = (N 1).testBit 2)
    {c : Nat} (hc : c % 4 = 1) :
    ∀ w ≥ 2, ∀ x, x.testBit 1 = false → ExactPeriod (hybridCarryNLFSR N c) w x (2 ^ (w - 1)) := by
  let F := hybridCarryNLFSR N c
  have hFc : Causal F := hybridCarryNLFSR_causal hN c
  let d := c / 4
  have hc_eq : c = 4 * d + 1 := by omega
  let U : Nat → Nat := fun q => q ^^^ (q <<< 1) ^^^ (N (4 * q) / 4)
  let V : Nat → Nat := fun q => q ^^^ (q <<< 1) ^^^ (N (4 * q + 1) / 4)
  let f1 : Nat → Nat := fun q => U q + d
  let f2 : Nat → Nat := fun q => V q + (d + 1)
  -- Step 1: F (4 * q) = 4 * f1 q + 1
  have hF_step1 : ∀ q, F (4 * q) = 4 * f1 q + 1 := by
    intro q
    have hu_eq : 4 * q ^^^ (4 * q) <<< 1 ^^^ N (4 * q) = 4 * U q := by
      apply Nat.eq_of_testBit_eq; intro k
      rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, testBit_four_mul, testBit_four_mul]
      match k with
      | 0 => simp [(hN.1 _).1]; omega
      | 1 =>
        simp only [show ¬(2 ≤ 1) by omega, show 1 ≤ 1 by omega, show 1 - 1 = 0 by omega,
                   show ¬(2 ≤ 0) by omega, (hN.1 _).2, decide_true, Bool.true_and, ↓reduceIte,
                   testBit_four_mul]; rfl
      | m + 2 =>
        have h1 : 1 ≤ m + 2 := by omega
        have h2 : 2 ≤ m + 2 := by omega
        have hsub : m + 2 - 1 = m + 1 := by omega
        have hsub2 : m + 2 - 2 = m := by omega
        simp only [h1, h2, hsub, hsub2, decide_true, Bool.true_and, ↓reduceIte, testBit_four_mul]
        dsimp only [U]
        rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, testBit_div_four]
        by_cases hm1 : 1 ≤ m
        · have h2m : 2 ≤ m + 1 := by omega
          have hs : m + 1 - 2 = m - 1 := by omega
          simp [hm1, h2m, hs]
        · have h2m : ¬(2 ≤ m + 1) := by omega
          simp [hm1, h2m]
    show (4 * q ^^^ (4 * q) <<< 1 ^^^ N (4 * q)) + c = 4 * (U q + d) + 1
    rw [hu_eq, hc_eq]; omega
  -- Step 2: F (4 * q + 1) = 4 * f2 q
  have hF_step2 : ∀ q, F (4 * q + 1) = 4 * f2 q := by
    intro q
    have hv_eq : (4 * q + 1) ^^^ (4 * q + 1) <<< 1 ^^^ N (4 * q + 1) = 4 * V q + 3 := by
      apply Nat.eq_of_testBit_eq; intro k
      rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft]
      have h4v3 : ∀ a i, (4 * a + 3).testBit i =
          if i < 2 then true else a.testBit (i - 2) := by
        intro a i
        match i with
        | 0 =>
          rw [testBit_eq_div_mod]
          have : (4 * a + 3) % 2 = 1 := by omega
          simp [this]
        | 1 =>
          rw [testBit_eq_div_mod]
          have : (4 * a + 3) / 2 ^ 1 % 2 = 1 := by omega
          simp [this]
        | m + 2 =>
          rw [testBit_eq_div_mod]
          have hdiv : (4 * a + 3) / 2 ^ (m + 2) = a / 2 ^ m := by
            rw [Nat.pow_add, show 2 ^ 2 = 4 by rfl, Nat.mul_comm (2 ^ m) 4, ← Nat.div_div_eq_div_mul]
            have : (4 * a + 3) / 4 = a := by omega
            rw [this]
          rw [hdiv, ← testBit_eq_div_mod]
          simp only [show ¬(m + 2 < 2) by omega, show m + 2 - 2 = m by omega, ↓reduceIte]
      rw [h4v3]
      match k with
      | 0 => simp [testBit_four_mul_add_one, (hN.1 _).1]
      | 1 => simp [testBit_four_mul_add_one, (hN.1 _).2]
      | m + 2 =>
        have h1 : 1 ≤ m + 2 := by omega
        have hlt2 : ¬(m + 2 < 2) := by omega
        have hsub1 : m + 2 - 1 = m + 1 := by omega
        have hsub2 : m + 2 - 2 = m := by omega
        simp only [h1, hlt2, hsub1, hsub2, decide_true, Bool.true_and, ↓reduceIte, testBit_four_mul_add_one]
        dsimp only [V]
        rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, testBit_div_four]
        by_cases hm1 : 1 ≤ m
        · have h2m : 2 ≤ m + 1 := by omega
          have hs : m + 1 - 2 = m - 1 := by omega
          simp [hm1, h2m, hs]
        · have h2m : ¬(2 ≤ m + 1) := by omega
          simp [hm1, h2m]
    show ((4 * q + 1) ^^^ (4 * q + 1) <<< 1 ^^^ N (4 * q + 1)) + c = 4 * (V q + (d + 1))
    rw [hv_eq, hc_eq]; omega
  -- Return map R(q) = F(F(4*q)) / 4 = f2 (f1 q)
  have hR_eq : ∀ q, returnMap F 2 0 2 q = f2 (f1 q) := by
    intro q
    unfold returnMap
    simp only [Nat.pow_two, Nat.add_zero, iter]
    rw [hF_step1, hF_step2]
    omega
  -- Prove U, V, f1, f2 are BitSlicedInvertible!
  have hN4_msb_blind : ∀ k q, k ≥ 1 → (N (4 * q) / 4).testBit k = (N (4 * (q % 2 ^ (k - 1))) / 4).testBit k := by
    intro k q hk
    rw [testBit_div_four, testBit_div_four]
    apply hN.testBit_mod_eq (by omega)
    have hpow : 2 ^ (k + 2 - 1) = 4 * 2 ^ (k - 1) := by
      have : k + 2 - 1 = 2 + (k - 1) := by omega
      rw [this, Nat.pow_add]
    rw [hpow, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_mod]
  have hN41_msb_blind : ∀ k q, k ≥ 1 → (N (4 * q + 1) / 4).testBit k = (N (4 * (q % 2 ^ (k - 1)) + 1) / 4).testBit k := by
    intro k q hk
    rw [testBit_div_four, testBit_div_four]
    apply hN.testBit_mod_eq (by omega)
    have hpow : 2 ^ (k + 2 - 1) = 4 * 2 ^ (k - 1) := by
      have : k + 2 - 1 = 2 + (k - 1) := by omega
      rw [this, Nat.pow_add]
    rw [hpow]
    have hmod : ∀ a, (4 * a + 1) % (4 * 2 ^ (k - 1)) = 4 * (a % 2 ^ (k - 1)) + 1 := by
      intro a
      have h1 : 4 * a + 1 = (4 * 2 ^ (k - 1)) * (a / 2 ^ (k - 1)) + (4 * (a % 2 ^ (k - 1)) + 1) := by
        rw [Nat.mul_assoc, ← Nat.add_assoc, ← Nat.mul_add, Nat.div_add_mod]
      have hlt : 4 * (a % 2 ^ (k - 1)) + 1 < 4 * 2 ^ (k - 1) := by
        have := Nat.mod_lt a (Nat.two_pow_pos (k - 1)); omega
      rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    rw [hmod q, hmod (q % 2 ^ (k - 1)), Nat.mod_mod]
  have hN4_mod : ∀ k q, (N (4 * q) / 4).testBit k = (N (4 * (q % 2 ^ k)) / 4).testBit k := by
    intro k q
    match k with
    | 0 =>
      rw [testBit_div_four, testBit_div_four]
      apply hN.testBit_mod_eq (by omega)
      simp; omega
    | m + 1 =>
      rw [hN4_msb_blind (m + 1) q (by omega), hN4_msb_blind (m + 1) (q % 2 ^ (m + 1)) (by omega)]
      have hdvd : 2 ^ m ∣ 2 ^ (m + 1) := by rw [Nat.pow_succ]; exact Nat.dvd_mul_right _ _
      simp [Nat.mod_mod_of_dvd _ hdvd]
  have hN41_mod : ∀ k q, (N (4 * q + 1) / 4).testBit k = (N (4 * (q % 2 ^ k) + 1) / 4).testBit k := by
    intro k q
    match k with
    | 0 =>
      rw [testBit_div_four, testBit_div_four]
      apply hN.testBit_mod_eq (by omega)
      simp; omega
    | m + 1 =>
      rw [hN41_msb_blind (m + 1) q (by omega), hN41_msb_blind (m + 1) (q % 2 ^ (m + 1)) (by omega)]
      have hdvd : 2 ^ m ∣ 2 ^ (m + 1) := by rw [Nat.pow_succ]; exact Nat.dvd_mul_right _ _
      simp [Nat.mod_mod_of_dvd _ hdvd]
  have hshift1_mod : ∀ k q, (q <<< 1).testBit k = ((q % 2 ^ k) <<< 1).testBit k := by
    intro k q
    rw [Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
    by_cases h1 : 1 ≤ k
    · rw [Nat.testBit_mod_two_pow]; simp [h1, (show k - 1 < k by omega)]
    · simp [h1]
  have hU_bsi : BitSlicedInvertible U (fun k q => xor ((q <<< 1).testBit k) ((N (4 * q) / 4).testBit k)) := by
    have hbit : ∀ k q, (U q).testBit k = xor (q.testBit k) (xor ((q <<< 1).testBit k) ((N (4 * q) / 4).testBit k)) := by
      intro k q; simp only [U, Nat.testBit_xor, bxor_assoc]
    refine ⟨?_, ?_⟩
    · intro w q1 q2 hq
      rw [mod_two_pow_eq_iff] at hq ⊢
      intro i hi
      rw [hbit i q1, hbit i q2, hq i hi, hshift1_mod i q1, hshift1_mod i q2, hN4_mod i q1, hN4_mod i q2]
      have hmi : q1 % 2 ^ i = q2 % 2 ^ i := (mod_two_pow_eq_iff i _ _).mpr (fun j hj => hq j (Nat.lt_trans hj hi))
      rw [hmi]
    · intro k q
      rw [hbit k q, hshift1_mod k q, hN4_mod k q]
  have hV_bsi : BitSlicedInvertible V (fun k q => xor ((q <<< 1).testBit k) ((N (4 * q + 1) / 4).testBit k)) := by
    have hbit : ∀ k q, (V q).testBit k = xor (q.testBit k) (xor ((q <<< 1).testBit k) ((N (4 * q + 1) / 4).testBit k)) := by
      intro k q; simp only [V, Nat.testBit_xor, bxor_assoc]
    refine ⟨?_, ?_⟩
    · intro w q1 q2 hq
      rw [mod_two_pow_eq_iff] at hq ⊢
      intro i hi
      rw [hbit i q1, hbit i q2, hq i hi, hshift1_mod i q1, hshift1_mod i q2, hN41_mod i q1, hN41_mod i q2]
      have hmi : q1 % 2 ^ i = q2 % 2 ^ i := (mod_two_pow_eq_iff i _ _).mpr (fun j hj => hq j (Nat.lt_trans hj hi))
      rw [hmi]
    · intro k q
      rw [hbit k q, hshift1_mod k q, hN41_mod k q]
  have hadd_bsi : ∀ m, BitSlicedInvertible (fun z => z + m) (fun k z => (z + m).testBit k) := by
    intro m
    refine ⟨?_, ?_⟩
    · intro w x y hxy
      rw [Nat.add_mod, Nat.add_mod y, hxy]
    · intro k x
      exact testBit_add_decomp x m k
  have hf1_bsi := hU_bsi.comp (hadd_bsi d)
  have hf2_bsi := hV_bsi.comp (hadd_bsi (d + 1))
  have hR_bsi_comp := hf1_bsi.comp hf2_bsi
  -- Rewrite R as `fun q => f2 (f1 q)`
  let R := fun q => f2 (f1 q)
  -- Base period at width 1 for R: R q % 2 = (q + 1) % 2!
  have hR_bit0 : ∀ q, (R q).testBit 0 = !(q.testBit 0) := by
    intro q
    have h := hR_bsi_comp.2 0 q
    simp only [Nat.pow_zero, Nat.mod_one, Nat.testBit_shiftLeft, Nat.zero_add,
               Nat.mul_zero, testBit_div_four] at h
    have hd_par : xor (d.testBit 0) ((d + 1).testBit 0) = true := by
      rw [testBit_eq_div_mod, testBit_eq_div_mod, Nat.pow_zero, Nat.div_one, Nat.div_one]
      rcases Nat.mod_two_eq_zero_or_one d with hd0 | hd1
      · have hd1' : (d + 1) % 2 = 1 := by omega
        simp [hd0, hd1']
      · have hd0' : (d + 1) % 2 = 0 := by omega
        simp [hd1, hd0']
    rw [h]
    simp only [show ¬(1 ≤ 0) by omega, decide_false, Bool.false_and, false_bxor]
    rw [hgate]
    have hre : xor (q.testBit 0) (xor (xor ((N 1).testBit 2) (d.testBit 0))
               (xor ((N 1).testBit 2) ((d + 1).testBit 0))) =
               xor (q.testBit 0) (xor (d.testBit 0) ((d + 1).testBit 0)) := by
      cases q.testBit 0 <;> cases (N 1).testBit 2 <;>
      cases d.testBit 0 <;> cases (d + 1).testBit 0 <;> rfl
    rw [hre, hd_par]
    cases q.testBit 0 <;> rfl
  have hR_base : ExactPeriod R 1 0 2 := by
    refine ⟨by omega, ?_, ?_⟩
    · rw [mod_two_pow_eq_iff]; intro i hi
      have hi0 : i = 0 := by omega
      rw [hi0]; simp only [iter, hR_bit0, Bool.not_not]
    · intro t htpos htlt heq
      have ht1 : t = 1 := by omega
      rw [ht1] at heq
      have h0 := (mod_two_pow_eq_iff 1 _ _).mp heq 0 (by omega)
      simp only [iter, hR_bit0] at h0
      cases hb : (0 : Nat).testBit 0 <;> simp [hb] at h0
  -- Full-cube holonomy of R at EVERY width k ≥ 1 is `true`!
  have hR_hol : ∀ k, k ≥ 1 →
      xorRange (2 ^ k) (fun q =>
        xor (xor (xor ((q <<< 1).testBit k) ((N (4 * q) / 4).testBit k)) ((U q % 2 ^ k + d).testBit k))
            (xor (xor (((f1 q % 2 ^ k) <<< 1).testBit k) ((N (4 * (f1 q % 2 ^ k) + 1) / 4).testBit k))
                 ((V (f1 q % 2 ^ k) % 2 ^ k + (d + 1)).testBit k))) = true := by
    intro k hk
    have hreg : ∀ q,
        xor (xor (xor ((q <<< 1).testBit k) ((N (4 * q) / 4).testBit k)) ((U q % 2 ^ k + d).testBit k))
            (xor (xor (((f1 q % 2 ^ k) <<< 1).testBit k) ((N (4 * (f1 q % 2 ^ k) + 1) / 4).testBit k))
                 ((V (f1 q % 2 ^ k) % 2 ^ k + (d + 1)).testBit k)) =
        xor (xor (xor ((q <<< 1).testBit k) (((f1 q % 2 ^ k) <<< 1).testBit k))
                 (xor ((N (4 * q) / 4).testBit k) ((N (4 * (f1 q % 2 ^ k) + 1) / 4).testBit k)))
            (xor ((U q % 2 ^ k + d).testBit k) ((V (f1 q % 2 ^ k) % 2 ^ k + (d + 1)).testBit k)) := by
      intro q
      cases (q <<< 1).testBit k <;> cases (N (4 * q) / 4).testBit k <;>
      cases (U q % 2 ^ k + d).testBit k <;> cases ((f1 q % 2 ^ k) <<< 1).testBit k <;>
      cases (N (4 * (f1 q % 2 ^ k) + 1) / 4).testBit k <;>
      cases (V (f1 q % 2 ^ k) % 2 ^ k + (d + 1)).testBit k <;> rfl
    rw [xorRange_congr (fun q _ => hreg q)]
    rw [xorRange_xor, xorRange_xor]
    conv => lhs; arg 1; arg 2; rw [xorRange_xor]
    conv => lhs; arg 2; rw [xorRange_xor]
    -- Term 1: Frobenius cancellation `q_{k-1} ^^ (f1 q)_{k-1}` is MSB-blind (`j = k - 1`)!
    have hT1 : xorRange (2 ^ k) (fun q => xor ((q <<< 1).testBit k) (((f1 q % 2 ^ k) <<< 1).testBit k)) = false := by
      apply any_bit_blind_xorRange_false (j := k - 1) (by omega)
      intro q _
      have h1 : ∀ z, xor ((z <<< 1).testBit k) (((f1 z % 2 ^ k) <<< 1).testBit k) =
          xor (xor (((z % 2 ^ (k - 1)) <<< 1).testBit (k - 1)) ((N (4 * (z % 2 ^ (k - 1))) / 4).testBit (k - 1)))
              ((U (z % 2 ^ (k - 1)) % 2 ^ (k - 1) + d).testBit (k - 1)) := by
        intro z
        rw [Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
        simp only [hk, decide_true, Bool.true_and]
        rw [Nat.testBit_mod_two_pow]
        simp only [show k - 1 < k by omega, decide_true, Bool.true_and]
        have hf1z := hf1_bsi.2 (k - 1) z
        change (z.testBit (k - 1) ^^ (f1 z).testBit (k - 1)) = _
        rw [hf1z]
        dsimp only
        cases z.testBit (k - 1) <;> cases ((z % 2 ^ (k - 1)) <<< 1).testBit (k - 1) <;>
        cases (N (4 * (z % 2 ^ (k - 1))) / 4).testBit (k - 1) <;>
        cases (U (z % 2 ^ (k - 1)) % 2 ^ (k - 1) + d).testBit (k - 1) <;> rfl
      rw [h1 (q ^^^ 2 ^ (k - 1)), h1 q]
      have hq_mod : (q ^^^ 2 ^ (k - 1)) % 2 ^ (k - 1) = q % 2 ^ (k - 1) := by
        rw [mod_two_pow_eq_iff]; intro i hi
        rw [Nat.testBit_xor, Nat.testBit_two_pow]
        simp [Nat.ne_of_gt hi]
      rw [hq_mod]
    -- Term 2: `N(4q)/4` at bit `k` is MSB-blind (`j = k - 1`)!
    have hT2 : xorRange (2 ^ k) (fun q => (N (4 * q) / 4).testBit k) = false := by
      apply any_bit_blind_xorRange_false (j := k - 1) (by omega)
      intro q _
      rw [hN4_msb_blind k (q ^^^ 2 ^ (k - 1)) hk, hN4_msb_blind k q hk]
      have hq_mod : (q ^^^ 2 ^ (k - 1)) % 2 ^ (k - 1) = q % 2 ^ (k - 1) := by
        rw [mod_two_pow_eq_iff]; intro i hi
        rw [Nat.testBit_xor, Nat.testBit_two_pow]; simp [Nat.ne_of_gt hi]
      rw [hq_mod]
    -- Term 3: `N(4*(f1 q % 2^k) + 1)/4` at bit `k` is MSB-blind after bijective reindexing by `f1`!
    have hT3 : xorRange (2 ^ k) (fun q => (N (4 * (f1 q % 2 ^ k) + 1) / 4).testBit k) = false := by
      rw [xorRange_bij f1 (fun z => (N (4 * z + 1) / 4).testBit k) (hf1_bsi.inj_mod k)]
      apply any_bit_blind_xorRange_false (j := k - 1) (by omega)
      intro q _
      rw [hN41_msb_blind k (q ^^^ 2 ^ (k - 1)) hk, hN41_msb_blind k q hk]
      have hq_mod : (q ^^^ 2 ^ (k - 1)) % 2 ^ (k - 1) = q % 2 ^ (k - 1) := by
        rw [mod_two_pow_eq_iff]; intro i hi
        rw [Nat.testBit_xor, Nat.testBit_two_pow]; simp [Nat.ne_of_gt hi]
      rw [hq_mod]
    -- Term 4: Carry parity of `U q % 2^k + d` = `d % 2 == 1`!
    have hT4 : xorRange (2 ^ k) (fun q => (U q % 2 ^ k + d).testBit k) = (d % 2 == 1) := by
      rw [xorRange_bij U (fun z => (z + d).testBit k) (hU_bsi.inj_mod k)]
      exact carry_xorRange_parity hk d
    -- Term 5: Carry parity of `V(f1 q % 2^k) % 2^k + (d + 1)` = `(d + 1) % 2 == 1`!
    have hT5 : xorRange (2 ^ k) (fun q => (V (f1 q % 2 ^ k) % 2 ^ k + (d + 1)).testBit k) = ((d + 1) % 2 == 1) := by
      have hcongr : ∀ q < 2 ^ k, (V (f1 q % 2 ^ k) % 2 ^ k + (d + 1)).testBit k =
                                  (V (f1 q) % 2 ^ k + (d + 1)).testBit k := by
        intro q _; rw [causal_mod hV_bsi.1]
      rw [xorRange_congr hcongr]
      have hVf1_bsi := hf1_bsi.comp hV_bsi
      rw [xorRange_bij (fun q => V (f1 q)) (fun z => (z + (d + 1)).testBit k) (hVf1_bsi.inj_mod k)]
      exact carry_xorRange_parity hk (d + 1)
    rw [hT1, hT2, hT3, hT4, hT5]
    rcases Nat.mod_two_eq_zero_or_one d with hd0 | hd1
    · have hd1' : (d + 1) % 2 = 1 := by omega
      simp [hd0, hd1']
    · have hd0' : (d + 1) % 2 = 0 := by omega
      simp [hd1, hd0']
  -- Lift R to full De Bruijn cycle at every width `m ≥ 1`!
  have hR_all : ∀ m, ExactPeriod R (1 + m) 0 (2 * 2 ^ m) := by
    apply cylinder_period_doubling hR_bsi_comp (fun _ => true) 1 2 0
      (fun _ _ => rfl) (by decide) rfl hR_base
    intro m
    have h1 := hR_hol (1 + m) (by omega)
    simpa only [↓reduceIte] using h1
  -- Translate `ExactPeriod R` to `ExactPeriod (returnMap F 2 0 2)` and lift via Engine 3A!
  have hF_base : ExactPeriod F 2 0 2 := by
    have h0 : F 0 = 4 * f1 0 + 1 := hF_step1 0
    have h1 : F 1 = 4 * f2 0 := hF_step2 0
    refine ⟨by omega, ?_, ?_⟩
    · simp only [iter, h0]
      rw [← causal_mod hFc 2 (4 * f1 0 + 1), show (4 * f1 0 + 1) % 2 ^ 2 = 1 by omega, h1]
      omega
    · intro t htpos htlt heq
      have ht1 : t = 1 := by omega
      rw [ht1] at heq
      simp only [iter, h0] at heq; omega
  have hP0_inv : ∀ y, (!y.testBit 1) = true → (!(F y).testBit 1) = true := by
    intro y hy
    have hy1 : y.testBit 1 = false := by simp at hy; exact hy
    have hmod : y % 4 = 0 ∨ y % 4 = 1 := by
      have hlt : y % 4 < 4 := Nat.mod_lt y (by omega)
      have hb : (y % 4).testBit 1 = false := by
        rw [show (4 : Nat) = 2 ^ 2 by rfl, Nat.testBit_mod_two_pow]; simp [hy1]
      have hcases : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
      rcases hcases with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · rw [h] at hb; exact absurd hb (by decide)
      · rw [h] at hb; exact absurd hb (by decide)
    have hFy_mod : F y % 4 = F (y % 4) % 4 := (causal_mod hFc 2 y).symm
    have hbit : (F y).testBit 1 = (F y % 4).testBit 1 := by
      rw [show (4 : Nat) = 2 ^ 2 by rfl, Nat.testBit_mod_two_pow]; simp
    rw [hbit, hFy_mod]
    rcases hmod with h0 | h1
    · rw [h0, hF_step1 0]; have : (4 * f1 0 + 1) % 4 = 1 := by omega
      rw [this]; rfl
    · rw [h1, hF_step2 0]; have : (4 * f2 0) % 4 = 0 := by omega
      rw [this]; rfl
  -- Combine for arbitrary `w ≥ 2` and `x` with `x.testBit 1 = false`!
  intro w hw x hx
  have hF_zero : ExactPeriod F w 0 (2 ^ (w - 1)) := by
    by_cases hw2 : w = 2
    · subst hw2; exact hF_base
    · have hw3 : w ≥ 3 := by omega
      let m := w - 3
      have hRm : ExactPeriod (returnMap F 2 0 2) (1 + m) 0 (2 * 2 ^ m) := by
        have hfun : returnMap F 2 0 2 = R := funext hR_eq
        rw [hfun]; exact hR_all m
      have hlift := returnMap_exactPeriod hFc (k0 := 2) (r := 0) (L := 2) (d := 1 + m) (q := 0) (M := 2 * 2 ^ m)
        (by omega) hF_base hRm
      have hw_eq : 2 + (1 + m) = w := by omega
      have hpow_eq : 2 * (2 * 2 ^ m) = 2 ^ (w - 1) := by
        have : w - 1 = 2 + m := by omega
        rw [this, Nat.pow_add]; omega
      simpa [hw_eq, hpow_eq] using hlift
  have hP0_inv_mod : ∀ z, (!(z % 2 ^ 2).testBit 1) = true → (!(F z % 2 ^ 2).testBit 1) = true := by
    intro z hz
    have hmod_bit : ∀ a, (a % 2 ^ 2).testBit 1 = a.testBit 1 := by
      intro a; rw [Nat.testBit_mod_two_pow]; simp
    rw [hmod_bit] at hz ⊢
    exact hP0_inv z hz
  have hres := exactPeriod_of_cylinder_mem hFc (P := fun z => !z.testBit 1)
    (w0 := 2) (d := w - 2) (L0 := 2) (x := 0) (y := x)
    hP0_inv_mod (by decide) (by decide)
    (by rw [Nat.testBit_mod_two_pow]; simp [hx])
    (by
      have hw_eq : 2 + (w - 2) = w := by omega
      have hpow_eq : 2 * 2 ^ (w - 2) = 2 ^ (w - 1) := by
        have : w - 1 = (w - 2) + 1 := by omega
        rw [this, Nat.pow_succ, Nat.mul_comm]
      rw [hw_eq, hpow_eq]; exact hF_zero)
  have hw_eq : 2 + (w - 2) = w := by omega
  have hpow_eq : 2 * 2 ^ (w - 2) = 2 ^ (w - 1) := by
    have : w - 1 = (w - 2) + 1 := by omega
    rw [this, Nat.pow_succ, Nat.mul_comm]
  rwa [hw_eq, hpow_eq] at hres

-- ----------------------------------------------------------------------------
-- THEOREM 2c: EXACT LOGARITHMIC PERIOD LAW ON THE CARRY-BARRIER SECTOR OF F0
--   For `F0(x) = (x ^^^ (x <<< 1)) + 1`, EVERY `w ≥ 3`, `k = ceil(log2(w - 1))`,
--   and EVERY `x` with `x.testBit 1 = true`:
--     `ExactPeriod F0 w x (2 ^ k)`!
-- ----------------------------------------------------------------------------

def A_lin (q : Nat) : Nat := q ^^^ (q <<< 1) ^^^ 1

/-- Exact characteristic-2 Frobenius power identity on all of `Nat` (no truncation needed!):
    `iter A_lin (2 ^ m) q = q ^^^ (q <<< 2 ^ m) ^^^ 2 ^ (2 ^ m - 1)`. -/
theorem iter_A_lin_pow2 (m q : Nat) :
    iter A_lin (2 ^ m) q = q ^^^ (q <<< 2 ^ m) ^^^ 2 ^ (2 ^ m - 1) := by
  induction m generalizing q with
  | zero =>
    simp [iter, A_lin]
  | succ m ih =>
    have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ, Nat.mul_two]
    rw [hpow, iter_add, ih, ih]
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_two_pow]
    have hpm : 2 ^ m ≥ 1 := Nat.two_pow_pos m
    by_cases hi : 2 ^ m ≤ i
    · have hi2 : (2 ^ m + 2 ^ m ≤ i) = (2 ^ m ≤ i - 2 ^ m) := by
        by_cases h : 2 ^ m + 2 ^ m ≤ i <;> simp [h] <;> omega
      have hsub : i - 2 ^ m - 2 ^ m = i - (2 ^ m + 2 ^ m) := by omega
      have hne1 : (2 ^ m - 1 = i) = false := by
        have : 2 ^ m - 1 ≠ i := by omega
        simp [this]
      have heq2 : (2 ^ m - 1 = i - 2 ^ m) = (2 ^ m + 2 ^ m - 1 = i) := by
        by_cases h : 2 ^ m - 1 = i - 2 ^ m <;> simp [h] <;> omega
      simp only [hi, decide_true, Bool.true_and, hne1, heq2, hi2, hsub]
      cases q.testBit i <;> cases q.testBit (i - 2 ^ m) <;>
      cases (decide (2 ^ m ≤ i - 2 ^ m) && q.testBit (i - (2 ^ m + 2 ^ m))) <;>
      cases decide (2 ^ m + 2 ^ m - 1 = i) <;> rfl
    · have hi2 : ¬(2 ^ m + 2 ^ m ≤ i) := by omega
      have hne2 : ¬(2 ^ m + 2 ^ m - 1 = i) := by omega
      simp only [hi, hi2, hne2, decide_false, Bool.false_and]
      cases q.testBit i <;> cases decide (2 ^ m - 1 = i) <;> rfl

/-- Elementary power-of-2 order lemma: if `iter f (2^k) x ≡ x` and `iter f (2^(k-1)) x ≢ x` mod `2^w`,
    then `2^k` is the EXACT minimal period! -/
theorem exactPeriod_of_pow2_witness {f : Nat → Nat} (hf : Causal f) {w x k : Nat}
    (hk : k ≥ 1)
    (hper : iter f (2 ^ k) x % 2 ^ w = x % 2 ^ w)
    (hne  : iter f (2 ^ (k - 1)) x % 2 ^ w ≠ x % 2 ^ w) :
    ExactPeriod f w x (2 ^ k) := by
  have hmod_step : ∀ a b, iter f a x % 2 ^ w = x % 2 ^ w → iter f b x % 2 ^ w = x % 2 ^ w →
      iter f (a % b) x % 2 ^ w = x % 2 ^ w := by
    intro a b ha hb
    by_cases hb0 : b = 0
    · subst hb0; simpa using ha
    · have hdiv : b * (a / b) + a % b = a := Nat.div_add_mod a b
      have h1 : iter f (a / b * b) x % 2 ^ w = x % 2 ^ w :=
        causal_iter_mul_period hf w x b hb (a / b)
      have h2 : iter f a x % 2 ^ w = iter f (a % b) (iter f (a / b * b) x) % 2 ^ w := by
        rw [← iter_add, Nat.mul_comm (a / b) b, hdiv]
      rw [ha, causal_iter hf w (a % b) _ _ h1] at h2
      exact h2.symm
  have hgcd : ∀ b a, iter f a x % 2 ^ w = x % 2 ^ w → iter f b x % 2 ^ w = x % 2 ^ w →
      iter f (Nat.gcd a b) x % 2 ^ w = x % 2 ^ w := by
    intro b
    refine Nat.strongRecOn b ?_
    intro b ih a ha hb
    by_cases hb0 : b = 0
    · subst hb0; simpa using ha
    · rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]
      exact ih (a % b) (Nat.mod_lt a (Nat.pos_of_ne_zero hb0)) b hb (hmod_step a b ha hb)
  refine ⟨Nat.two_pow_pos k, hper, ?_⟩
  intro t htpos htlt htper
  let g := Nat.gcd t (2 ^ k)
  have hg_per : iter f g x % 2 ^ w = x % 2 ^ w := hgcd (2 ^ k) t htper hper
  have hg_dvd : g ∣ 2 ^ k := Nat.gcd_dvd_right t (2 ^ k)
  have hg_le : g ≤ t := Nat.le_of_dvd htpos (Nat.gcd_dvd_left t (2 ^ k))
  have hg_lt : g < 2 ^ k := Nat.lt_of_le_of_lt hg_le htlt
  have hg_dvd_half : g ∣ 2 ^ (k - 1) := by
    rcases hg_dvd with ⟨q, hq⟩
    have hq_ge2 : q ≥ 2 := by
      cases q with
      | zero => simp at hq
      | succ m =>
        cases m with
        | zero => simp at hq; omega
        | succ _ => omega
    have h2dvd : 2 ∣ q := by
      have hq_dvd_2k : q ∣ 2 ^ k := ⟨g, by rw [Nat.mul_comm]; exact hq⟩
      have hq_even : q % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one q with h0 | h1
        · exact h0
        · exfalso
          have hcop : ∀ m, Nat.gcd q (2 ^ m) = 1 := by
            intro m; induction m with
            | zero => simp
            | succ m ihm =>
              have hcop2 : Nat.gcd q 2 = 1 := by
                rw [Nat.gcd_comm, Nat.gcd_rec, h1]; rfl
              rw [Nat.pow_succ]
              exact Nat.Coprime.mul_right ihm hcop2
          have h1eq : Nat.gcd q (2 ^ k) = q := Nat.gcd_eq_left hq_dvd_2k
          rw [hcop k] at h1eq
          omega
      exact Nat.dvd_of_mod_eq_zero hq_even
    rcases h2dvd with ⟨q', rfl⟩
    refine ⟨q', ?_⟩
    have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
      conv => lhs; rw [show k = (k - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have h2eq : 2 * 2 ^ (k - 1) = 2 * (g * q') := by
      rw [← h2k, hq]; rw [Nat.mul_left_comm]
    exact Nat.eq_of_mul_eq_mul_left (by omega) h2eq
  rcases hg_dvd_half with ⟨m, hm⟩
  have hhalf : iter f (2 ^ (k - 1)) x % 2 ^ w = x % 2 ^ w := by
    rw [hm, Nat.mul_comm g m]
    exact causal_iter_mul_period hf w x g hg_per m
  exact hne hhalf

theorem F0_zero_twoDelayed : TwoDelayed (fun _ => 0) :=
  ⟨fun _ => ⟨Nat.zero_testBit 0, Nat.zero_testBit 1⟩, fun _ _ _ => rfl⟩

/-- THEOREM 2c (Exact Logarithmic Period Law on Carry-Barrier Sector of `F0(x) = (x ^^^ (x <<< 1)) + 1`):
    For EVERY `w ≥ 3`, EVERY `k ≥ 1` with `2^(k - 1) < w - 1 ≤ 2^k` (i.e. `k = ceil(log2(w - 1))`),
    and EVERY `x` in the Carry-Barrier Sector (`x.testBit 1 = true`):
      `ExactPeriod F0 w x (2 ^ k)`! -/
theorem theorem2c_linear_carry_barrier_exact_log_period
    (w k : Nat) (hw : w ≥ 3) (hk : k ≥ 1)
    (hhi : w - 1 ≤ 2 ^ k) (hlo : 2 ^ (k - 1) < w - 1)
    (x : Nat) (hx : x.testBit 1 = true) :
    ExactPeriod F0 w x (2 ^ k) := by
  have hF0_eq : ∀ z, F0 z = hybridCarryNLFSR (fun _ => 0) 1 z := by
    intro z; simp [F0, hybridCarryNLFSR]
  have hF0c : Causal F0 := by
    intro a b c h; rw [hF0_eq, hF0_eq]; exact hybridCarryNLFSR_causal F0_zero_twoDelayed 1 a b c h
  -- Step relation on `x.testBit 1 = true`:
  have hstep : ∀ z, z.testBit 1 = true →
      (F0 z).testBit 1 = true ∧
      (F0 z).testBit 0 = !(z.testBit 0) ∧
      F0 z / 4 = A_lin (z / 4) := by
    intro z hz
    have hbar := theorem2b_carry_barrier_hermetic F0_zero_twoDelayed z hz
    rw [← hF0_eq z] at hbar
    have hbit0 : (F0 z).testBit 0 = !(z.testBit 0) := by
      unfold F0
      rw [testBit_add_decomp, Nat.testBit_xor, Nat.testBit_shiftLeft]
      simp only [show ¬(1 ≤ 0) by omega, decide_false, Bool.false_and, bxor_false,
                 Nat.pow_zero, Nat.mod_one]
      cases z.testBit 0 <;> rfl
    have hdiv4 : F0 z / 4 = A_lin (z / 4) := by
      rw [hbar.2]
      simp only [Nat.xor_zero]
      apply Nat.eq_of_testBit_eq; intro i
      rw [testBit_div_four, Nat.testBit_xor, Nat.testBit_shiftLeft]
      unfold A_lin
      rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, testBit_div_four]
      match i with
      | 0 => simp [hz]
      | m + 1 =>
        have h1 : (1 : Nat).testBit (m + 1) = false := by
          rw [testBit_eq_div_mod]
          have : 1 / 2 ^ (m + 1) = 0 := Nat.div_eq_of_lt (by have := Nat.two_pow_pos m; rw [Nat.pow_succ]; omega)
          simp [this]
        have h1a : 1 ≤ m + 1 + 2 := by omega
        have h1b : 1 ≤ m + 1 := by omega
        have hsub : m + 1 + 2 - 1 = m + 2 := by omega
        simp [h1, h1a, h1b, hsub, testBit_div_four]
    exact ⟨hbar.1, hbit0, hdiv4⟩
  -- Iterated dynamics on the Carry-Barrier Sector!
  have hiter_inv : ∀ t, (iter F0 t x).testBit 1 = true ∧
      (iter F0 t x).testBit 0 = (if t % 2 = 0 then x.testBit 0 else !(x.testBit 0)) ∧
      iter F0 t x / 4 = iter A_lin t (x / 4) := by
    intro t; induction t with
    | zero => simp [iter, hx]
    | succ t ih =>
      have hs := hstep (iter F0 t x) ih.1
      refine ⟨hs.1, ?_, ?_⟩
      · rw [iter_succ, hs.2.1, ih.2.1]
        rcases Nat.mod_two_eq_zero_or_one t with ht0 | ht1
        · have ht1' : (t + 1) % 2 = 1 := by omega
          simp [ht0, ht1']
        · have ht0' : (t + 1) % 2 = 0 := by omega
          simp [ht1, ht0']
      · rw [iter_succ, hs.2.2, ih.2.2, iter_succ]
  apply exactPeriod_of_pow2_witness hF0c hk
  · -- Periodicity at 2^k mod 2^w
    rw [mod_two_pow_eq_iff]; intro i hi
    have h2k_even : 2 ^ k % 2 = 0 := by
      have : 2 ^ k = 2 * 2 ^ (k - 1) := by
        conv => lhs; rw [show k = (k - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
      omega
    match i with
    | 0 => simp [(hiter_inv (2 ^ k)).2.1, h2k_even]
    | 1 => rw [(hiter_inv (2 ^ k)).1, hx]
    | m + 2 =>
      rw [← testBit_div_four, (hiter_inv (2 ^ k)).2.2, iter_A_lin_pow2,
          Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_two_pow,
          testBit_div_four]
      have hm_lt1 : ¬(2 ^ k ≤ m) := by omega
      have hm_ne : 2 ^ k - 1 ≠ m := by omega
      simp [hm_lt1, hm_ne]
  · -- Non-periodicity at 2^(k-1) mod 2^w!
    intro heq
    by_cases hk1 : k = 1
    · subst hk1
      have h0 := (mod_two_pow_eq_iff w _ _).mp heq 0 (by omega)
      have hi0 := (hiter_inv 1).2.1
      simp only [show (1 : Nat) % 2 ≠ 0 by omega, ↓reduceIte] at hi0
      rw [Nat.pow_zero] at h0
      rw [hi0] at h0
      cases hb : x.testBit 0 <;> simp [hb] at h0
    · have hk2 : k ≥ 2 := by omega
      let m := 2 ^ (k - 1) - 1
      have hm_lt : m + 2 < w := by omega
      have hbit := (mod_two_pow_eq_iff w _ _).mp heq (m + 2) hm_lt
      rw [← testBit_div_four, (hiter_inv (2 ^ (k - 1))).2.2, iter_A_lin_pow2,
          Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_two_pow,
          testBit_div_four] at hbit
      have hmlt : ¬(2 ^ (k - 1) ≤ m) := by
        have := Nat.two_pow_pos (k - 1); omega
      have hmeq : 2 ^ (k - 1) - 1 = m := rfl
      simp only [hmlt, decide_false, Bool.false_and, bxor_false, hmeq, decide_true] at hbit
      cases hb : x.testBit (m + 2) <;> simp [hb] at hbit

-- ============================================================================
-- PART V-C: THEOREM 3 — EXACT NON-PREFIX DE BRUIJN COMPLETENESS & INFINITE
--           PREFIX-LENGTH-d CYCLE-SPLITTING SHARPNESS
-- ============================================================================

theorem evalTap_testBit {T : List Nat} (hT : T ≠ []) (x k : Nat) :
    (evalTap T x).testBit k = T.all (fun s => decide (s ≤ k) && x.testBit (k - s)) := by
  induction T with
  | nil => exact absurd rfl hT
  | cons s rest ih =>
    cases rest with
    | nil => simp [evalTap, Nat.testBit_shiftLeft]
    | cons s2 rest2 =>
      simp only [evalTap, Nat.testBit_and, Nat.testBit_shiftLeft, List.all_cons]
      rw [ih (List.cons_ne_nil _ _), List.all_cons]

theorem evalTap_mod {T : List Nat} (hpos : ∀ s ∈ T, 1 ≤ s) (x k : Nat) :
    (evalTap T x).testBit k = (evalTap T (x % 2 ^ k)).testBit k := by
  cases T with
  | nil => rfl
  | cons s rest =>
    rw [evalTap_testBit (List.cons_ne_nil _ _), evalTap_testBit (List.cons_ne_nil _ _)]
    have hcongr : ∀ (ls : List Nat), (∀ u ∈ ls, 1 ≤ u) →
        ls.all (fun u => decide (u ≤ k) && x.testBit (k - u)) =
        ls.all (fun u => decide (u ≤ k) && (x % 2 ^ k).testBit (k - u)) := by
      intro ls hls; induction ls with
      | nil => rfl
      | cons u us ihu =>
        simp only [List.all_cons]
        have hu1 : 1 ≤ u := hls u List.mem_cons_self
        have hbit : (decide (u ≤ k) && x.testBit (k - u)) =
                    (decide (u ≤ k) && (x % 2 ^ k).testBit (k - u)) := by
          by_cases huk : u ≤ k
          · rw [Nat.testBit_mod_two_pow]
            simp [huk, show k - u < k by omega]
          · simp [huk]
        rw [hbit, ihu (fun v hv => hls v (List.mem_cons_of_mem _ hv))]
    exact hcongr (s :: rest) hpos

theorem evalPoly_testBit (M : List (List Nat)) (x k : Nat) :
    (evalPoly M x).testBit k =
    M.foldr (fun T acc => xor ((evalTap T x).testBit k) acc) false := by
  induction M with
  | nil => simp [evalPoly]
  | cons T rest ih => simp [evalPoly, Nat.testBit_xor, ih]

theorem evalPoly_mod {M : List (List Nat)} (hM : ∀ T ∈ M, ∀ s ∈ T, 1 ≤ s) (x k : Nat) :
    (evalPoly M x).testBit k = (evalPoly M (x % 2 ^ k)).testBit k := by
  induction M with
  | nil => rfl
  | cons T rest ih =>
    simp only [evalPoly, Nat.testBit_xor]
    rw [evalTap_mod (hM T List.mem_cons_self),
        ih (fun T' hT' => hM T' (List.mem_cons_of_mem _ hT'))]

theorem evalPoly_xor_bsi {M : List (List Nat)} (hM : ∀ T ∈ M, ∀ s ∈ T, 1 ≤ s) :
    BitSlicedInvertible (fun x => x ^^^ evalPoly M x) (fun k y => (evalPoly M y).testBit k) := by
  refine ⟨?_, ?_⟩
  · intro w x y hxy
    rw [mod_two_pow_eq_iff] at hxy ⊢
    intro i hi
    simp only [Nat.testBit_xor]
    rw [hxy i hi, evalPoly_mod hM x i, evalPoly_mod hM y i]
    have hmi : x % 2 ^ i = y % 2 ^ i := (mod_two_pow_eq_iff i _ _).mpr (fun j hj => hxy j (Nat.lt_trans hj hi))
    rw [hmi]
  · intro k x
    rw [Nat.testBit_xor, evalPoly_mod hM x k]

theorem hybridTapNLFSR_bsi {M : List (List Nat)} (hM : ∀ T ∈ M, ∀ s ∈ T, 1 ≤ s) (c : Nat) :
    BitSlicedInvertible (hybridTapNLFSR M c)
      (fun k y => xor ((evalPoly M y).testBit k) (((y ^^^ evalPoly M y) % 2 ^ k + c).testBit k)) := by
  have h1 := evalPoly_xor_bsi hM
  have h2 : BitSlicedInvertible (fun z => z + c) (fun k z => (z + c).testBit k) :=
    ⟨fun w x y hxy => by rw [Nat.add_mod, Nat.add_mod y, hxy], fun k x => testBit_add_decomp x c k⟩
  exact h1.comp h2

/-- Every non-prefix tap has vanishing full-cube XOR sum at EVERY width `w ≥ 1`! -/
theorem evalTap_nonprefix_xorRange_false {T : List Nat} (hT : NonPrefixTap T) {w : Nat} (_hw : w ≥ 1) :
    xorRange (2 ^ w) (fun y => (evalTap T y).testBit w) = false := by
  rcases hT with ⟨hne, hpos, g, hg1, ⟨smax, hsmax_in, hgs⟩, hg_not⟩
  by_cases hws : smax ≤ w
  · -- Flip bit `j = w - g < w`; since `g ∉ T`, no tap in `T` reads bit `w - g`!
    apply any_bit_blind_xorRange_false (j := w - g) (by omega)
    intro y _
    rw [evalTap_testBit hne, evalTap_testBit hne]
    have hcongr : ∀ (ls : List Nat), (∀ s ∈ ls, s ≠ g) →
        ls.all (fun s => decide (s ≤ w) && (y ^^^ 2 ^ (w - g)).testBit (w - s)) =
        ls.all (fun s => decide (s ≤ w) && y.testBit (w - s)) := by
      intro ls hls; induction ls with
      | nil => rfl
      | cons s ss ih =>
        simp only [List.all_cons]
        have hsg : s ≠ g := hls s List.mem_cons_self
        have hbit : (decide (s ≤ w) && (y ^^^ 2 ^ (w - g)).testBit (w - s)) =
                    (decide (s ≤ w) && y.testBit (w - s)) := by
          by_cases hsw : s ≤ w
          · rw [Nat.testBit_xor, Nat.testBit_two_pow]
            have hne_idx : w - g ≠ w - s := by omega
            simp [hsw, hne_idx]
          · simp [hsw]
        rw [hbit, ih (fun u hu => hls u (List.mem_cons_of_mem _ hu))]
    exact hcongr T (fun s hs hEq => hg_not (hEq ▸ hs))
  · -- `w < smax`, so `(evalTap T y).testBit w = false` identically!
    have hzero : ∀ y < 2 ^ w, (evalTap T y).testBit w = false := by
      intro y _
      rw [evalTap_testBit hne]
      have hall_false : ∀ (ls : List Nat), smax ∈ ls →
          ls.all (fun s => decide (s ≤ w) && y.testBit (w - s)) = false := by
        intro ls hls; induction ls with
        | nil => contradiction
        | cons s ss ih =>
          simp only [List.all_cons]
          rcases List.mem_cons.mp hls with rfl | hss
          · simp [hws]
          · rw [ih hss, Bool.and_false]
      exact hall_false T hsmax_in
    rw [xorRange_congr hzero, xorRange_false]

/-- THEOREM 3a (Universal De Bruijn Completeness for Arbitrary Non-Prefix Hybrid XOR-AND-Carry NLFSRs):
    For EVERY finite collection `M` of non-prefix multi-way AND taps, EVERY odd `c`, and EVERY `w ≥ 1`:
      `SingleCycle (hybridTapNLFSR M c) w`! -/
theorem theorem3a_nonprefix_hybrid_nlfsr_debruijn
    {M : List (List Nat)} (hM : ∀ T ∈ M, NonPrefixTap T)
    {c : Nat} (hc : c % 2 = 1) (w : Nat) (hw : w ≥ 1) :
    SingleCycle (hybridTapNLFSR M c) w := by
  have hMpos : ∀ T ∈ M, ∀ s ∈ T, 1 ≤ s := fun T hT => (hM T hT).2.1
  have hbsi := hybridTapNLFSR_bsi hMpos c
  have hbase : ExactPeriod (hybridTapNLFSR M c) 1 0 2 := by
    have hbit0 : ∀ x, (hybridTapNLFSR M c x).testBit 0 = !(x.testBit 0) := by
      intro x
      have h := hbsi.2 0 x
      have hpoly0 : ∀ (ls : List (List Nat)), (∀ T ∈ ls, ∀ s ∈ T, 1 ≤ s) → (evalPoly ls (x % 2 ^ 0)).testBit 0 = false := by
        intro ls hls; induction ls with
        | nil => simp [evalPoly]
        | cons T rest ih =>
          simp only [evalPoly, Nat.testBit_xor]
          have hT0 : (evalTap T (x % 2 ^ 0)).testBit 0 = false := by
            cases T with
            | nil => simp [evalTap]
            | cons s ss =>
              rw [evalTap_testBit (List.cons_ne_nil _ _)]
              have hs1 : 1 ≤ s := hls (s :: ss) List.mem_cons_self s List.mem_cons_self
              simp only [List.all_cons, show ¬(s ≤ 0) by omega, decide_false, Bool.false_and]
          rw [hT0, ih (fun T' hT' => hls T' (List.mem_cons_of_mem _ hT'))]; rfl
      rw [h]; dsimp only; rw [hpoly0 M hMpos]
      simp only [Nat.pow_zero, Nat.mod_one, false_bxor, Nat.zero_add]
      rw [testBit_eq_div_mod c 0, Nat.pow_zero, Nat.div_one, hc]
      cases x.testBit 0 <;> rfl
    refine ⟨by omega, ?_, ?_⟩
    · rw [mod_two_pow_eq_iff]; intro i hi
      have hi0 : i = 0 := by omega
      rw [hi0]; simp only [iter, hbit0, Bool.not_not]
    · intro t htpos htlt heq
      have ht1 : t = 1 := by omega
      rw [ht1] at heq
      have h0 := (mod_two_pow_eq_iff 1 _ _).mp heq 0 (by omega)
      simp only [iter, hbit0] at h0
      cases hb : (0 : Nat).testBit 0 <;> simp [hb] at h0
  have hall : ∀ d, ExactPeriod (hybridTapNLFSR M c) (1 + d) 0 (2 * 2 ^ d) := by
    apply cylinder_period_doubling hbsi (fun _ => true) 1 2 0
      (fun _ _ => rfl) (by decide) rfl hbase
    intro d
    let k := 1 + d
    have hk : k ≥ 1 := by omega
    simp only [↓reduceIte]
    rw [xorRange_xor]
    have hpoly_zero : ∀ (ls : List (List Nat)), (∀ T ∈ ls, NonPrefixTap T) →
        xorRange (2 ^ k) (fun y => (evalPoly ls y).testBit k) = false := by
      intro ls hls; induction ls with
      | nil =>
        have h0 : ∀ y < 2 ^ k, (evalPoly [] y).testBit k = false := fun _ _ => by simp [evalPoly]
        rw [xorRange_congr h0, xorRange_false]
      | cons T rest ih =>
        have hcongr : ∀ y < 2 ^ k, (evalPoly (T :: rest) y).testBit k =
            xor ((evalTap T y).testBit k) ((evalPoly rest y).testBit k) := by
          intro y _; simp [evalPoly, Nat.testBit_xor]
        rw [xorRange_congr hcongr, xorRange_xor,
            evalTap_nonprefix_xorRange_false (hls T List.mem_cons_self) hk,
            ih (fun T' hT' => hls T' (List.mem_cons_of_mem _ hT'))]
        rfl
    -- Part 2: carry XOR sum is `true` because `c` is odd and `y ↦ y ^^^ evalPoly M y` is bijective!
    have hcarry_one : xorRange (2 ^ k) (fun y => ((y ^^^ evalPoly M y) % 2 ^ k + c).testBit k) = true := by
      rw [xorRange_bij (fun y => y ^^^ evalPoly M y) (fun z => (z + c).testBit k)
            ((evalPoly_xor_bsi hMpos).inj_mod k),
          carry_xorRange_parity hk c, hc]
      rfl
    rw [hpoly_zero M hM, hcarry_one]; rfl
  have hd := hall (w - 1)
  have hw_eq : 1 + (w - 1) = w := by omega
  have hpow : 2 * 2 ^ (w - 1) = 2 ^ w := by
    conv => rhs; rw [show w = (w - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  rw [hw_eq, hpow] at hd
  exact singleCycle_of_zero hbsi.1 hd

theorem prefixTap_mem (d s : Nat) : s ∈ prefixTap d ↔ 1 ≤ s ∧ s ≤ d := by
  unfold prefixTap
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have := List.mem_range.mp hi; omega
  · rintro ⟨hs1, hsd⟩
    exact ⟨s - 1, List.mem_range.mpr (by omega), by omega⟩

/-- THEOREM 3b (Infinite Prefix-Length-`d` Exact Cycle-Splitting Sharpness Theorem):
    For EVERY `d ≥ 1` and EVERY odd `c`, consider `F := hybridTapNLFSR [prefixTap d] c`.
    1. For ALL `1 ≤ w ≤ d`: `F` is De Bruijn complete (`SingleCycle F w`).
    2. At `w = d + 1`: `F` undergoes EXACT 2-WAY CYCLE SPLITTING into two disjoint cycles
       of exact length `2^d` (anchored at `0` and `2^d`)! -/
theorem theorem3b_prefix_tap_exact_cycle_splitting
    (d : Nat) (hd : d ≥ 1) {c : Nat} (hc : c % 2 = 1) :
    (∀ w, 1 ≤ w → w ≤ d → SingleCycle (hybridTapNLFSR [prefixTap d] c) w) ∧
    (ExactPeriod (hybridTapNLFSR [prefixTap d] c) (d + 1) 0 (2 ^ d) ∧
     ExactPeriod (hybridTapNLFSR [prefixTap d] c) (d + 1) (2 ^ d) (2 ^ d) ∧
     ∀ t, iter (hybridTapNLFSR [prefixTap d] c) t 0 % 2 ^ (d + 1) ≠ 2 ^ d % 2 ^ (d + 1)) := by
  let P := prefixTap d
  let F := hybridTapNLFSR [P] c
  have hPne : P ≠ [] := by
    intro h
    have : 1 ∈ P := (prefixTap_mem d 1).mpr ⟨Nat.le_refl 1, hd⟩
    rw [h] at this; contradiction
  have hMpos : ∀ T ∈ [P], ∀ s ∈ T, 1 ≤ s := by
    intro T hT s hs
    simp at hT; subst hT
    exact ((prefixTap_mem d s).mp hs).1
  have hbsi := hybridTapNLFSR_bsi hMpos c
  -- For any `k < d`, `(evalTap P y).testBit k = false` identically!
  have hbelow : ∀ k < d, ∀ y, (evalTap P y).testBit k = false := by
    intro k hk y
    rw [evalTap_testBit hPne]
    have hd_in : d ∈ P := (prefixTap_mem d d).mpr ⟨hd, Nat.le_refl d⟩
    have hfalse : ∀ (ls : List Nat), d ∈ ls → ls.all (fun s => decide (s ≤ k) && y.testBit (k - s)) = false := by
      intro ls hls; induction ls with
      | nil => contradiction
      | cons s ss ih =>
        simp only [List.all_cons]
        rcases List.mem_cons.mp hls with rfl | hss
        · simp [show ¬(d ≤ k) by omega]
        · rw [ih hss, Bool.and_false]
    exact hfalse P hd_in
  -- Base period at `w = 1`
  have hbase : ExactPeriod F 1 0 2 := by
    have hbit0 : ∀ x, (F x).testBit 0 = !(x.testBit 0) := by
      intro x
      have h := hbsi.2 0 x
      change (F x).testBit 0 = _ at h
      rw [h]; dsimp only
      simp only [evalPoly, Nat.xor_zero, hbelow 0 (by omega), false_bxor,
                 Nat.pow_zero, Nat.mod_one, Nat.zero_add]
      rw [testBit_eq_div_mod c 0, Nat.pow_zero, Nat.div_one, hc]
      cases x.testBit 0 <;> rfl
    refine ⟨by omega, ?_, ?_⟩
    · rw [mod_two_pow_eq_iff]; intro i hi
      have hi0 : i = 0 := by omega
      rw [hi0]; simp only [iter, hbit0, Bool.not_not]
    · intro t htpos htlt heq
      have ht1 : t = 1 := by omega
      rw [ht1] at heq
      have h0 := (mod_two_pow_eq_iff 1 _ _).mp heq 0 (by omega)
      simp only [iter, hbit0] at h0
      cases hb : (0 : Nat).testBit 0 <;> simp [hb] at h0
  -- Inductive lift for all `1 ≤ w ≤ d`!
  have hlift_le : ∀ w, 1 ≤ w → w ≤ d → ExactPeriod F w 0 (2 ^ w) := by
    intro w hw1 hwd
    induction w with
    | zero => omega
    | succ m ih =>
      by_cases hm0 : m = 0
      · subst hm0; exact hbase
      · have ih' := ih (by omega) (by omega)
        have hstep := exactPeriod_lift_double hbsi ih' (by
          rw [cycleHolonomy]
          have horb_in : ∀ t < 2 ^ m, iter F t 0 % 2 ^ m < 2 ^ m ∧ true = true :=
            fun t _ => ⟨Nat.mod_lt _ (Nat.two_pow_pos m), rfl⟩
          have horb_inj := orbit_inj_of_exactPeriod hbsi.1 ih'
          have hcnt : ((List.range (2 ^ m)).filter (fun _ => true)).length = 2 ^ m := by
            have hf : ∀ (ls : List Nat), ls.filter (fun _ => true) = ls := by
              intro ls; induction ls with | nil => rfl | cons _ _ ihf => simp [ihf]
            rw [hf, List.length_range]
          have hbij := xorRange_eq_filtered_of_inj
            (fun t => iter F t 0 % 2 ^ m) (fun _ => true)
            (fun y => xor ((evalPoly [P] y).testBit m) (((y ^^^ evalPoly [P] y) % 2 ^ m + c).testBit m))
            horb_in horb_inj hcnt
          change xorRange (2 ^ m) (fun t =>
            xor ((evalPoly [P] (iter F t 0 % 2 ^ m)).testBit m)
                ((((iter F t 0 % 2 ^ m) ^^^ evalPoly [P] (iter F t 0 % 2 ^ m)) % 2 ^ m + c).testBit m)) = true
          rw [hbij]
          simp only [↓reduceIte, evalPoly, Nat.xor_zero, hbelow m (by omega), false_bxor]
          have hcongr : ∀ y < 2 ^ m, ((y ^^^ evalTap P y) % 2 ^ m + c).testBit m = (y + c).testBit m := by
            intro y hy
            have hy_lt : (y ^^^ evalTap P y) % 2 ^ m = y := by
              rw [← Nat.mod_eq_of_lt hy]
              rw [mod_two_pow_eq_iff]; intro i hi
              rw [Nat.testBit_xor, hbelow i (by omega), bxor_false, Nat.testBit_mod_two_pow]
              simp [hi]
            rw [hy_lt]
          rw [xorRange_congr hcongr, carry_xorRange_parity (by omega) c, hc]; rfl)
        rw [Nat.pow_succ, Nat.mul_comm]
        exact hstep
  have hsingle_le : ∀ w, 1 ≤ w → w ≤ d → SingleCycle F w :=
    fun w hw1 hwd => singleCycle_of_zero hbsi.1 (hlift_le w hw1 hwd)
  -- At width `d`, `(evalTap P y).testBit d = true` IFF `y = 2^d - 1` (for `y < 2^d`)!
  have htap_at_d : ∀ y < 2 ^ d, (evalTap P y).testBit d = (y == 2 ^ d - 1) := by
    intro y hy
    rw [evalTap_testBit hPne]
    have hiff : P.all (fun s => decide (s ≤ d) && y.testBit (d - s)) = true ↔ y = 2 ^ d - 1 := by
      rw [List.all_eq_true]
      constructor
      · intro hall
        apply Nat.eq_of_testBit_eq; intro i
        by_cases hid : i < d
        · have hs_in : d - i ∈ P := (prefixTap_mem d (d - i)).mpr ⟨by omega, by omega⟩
          have hb := hall (d - i) hs_in
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
          have hsub : d - (d - i) = i := by omega
          rw [hsub] at hb
          rw [hb.2, Nat.testBit_two_pow_sub_one]; simp [hid]
        · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega)))]
          rw [Nat.testBit_two_pow_sub_one]; simp [hid]
      · rintro rfl s hs
        have hsr := (prefixTap_mem d s).mp hs
        simp only [Bool.and_eq_true, decide_eq_true_eq, hsr.2, true_and]
        rw [Nat.testBit_two_pow_sub_one]
        simp [show d - s < d by omega]
    cases hb : P.all (fun s => decide (s ≤ d) && y.testBit (d - s))
    · have hne : y ≠ 2 ^ d - 1 := fun h => by have := hiff.mpr h; rw [hb] at this; contradiction
      simp [hne]
    · have heq := hiff.mp hb
      simp [heq]
  -- Therefore the cube XOR sum of `(evalTap P y).testBit d` is `true` (single 1 at `y = 2^d - 1`)!
  have htap_sum : xorRange (2 ^ d) (fun y => (evalTap P y).testBit d) = true := by
    rw [xorRange_congr htap_at_d]
    let m := 2 ^ d - 1
    have hsplit : 2 ^ d = m + 1 := (Nat.sub_add_cancel (Nat.two_pow_pos d)).symm
    have hlo : xorRange m (fun y => y == m) = false := by
      have : ∀ y < m, (y == m) = false := fun y hy => beq_false_of_ne (by omega)
      rw [xorRange_congr this, xorRange_false]
    change xorRange (2 ^ d) (fun y => y == m) = true
    rw [hsplit, xorRange, hlo]; simp
  -- Thus cycle holonomy at width `d` is `true ^^ true = false`, triggering EXACT CYCLE-SPLITTING!
  have hEd := hlift_le d hd (Nat.le_refl d)
  have hhol_false : cycleHolonomy F
      (fun k y => xor ((evalPoly [P] y).testBit k) (((y ^^^ evalPoly [P] y) % 2 ^ k + c).testBit k))
      d 0 (2 ^ d) = false := by
    rw [cycleHolonomy]
    have horb_in : ∀ t < 2 ^ d, iter F t 0 % 2 ^ d < 2 ^ d ∧ true = true :=
      fun t _ => ⟨Nat.mod_lt _ (Nat.two_pow_pos d), rfl⟩
    have horb_inj := orbit_inj_of_exactPeriod hbsi.1 hEd
    have hcnt : ((List.range (2 ^ d)).filter (fun _ => true)).length = 2 ^ d := by
      have hf : ∀ (ls : List Nat), ls.filter (fun _ => true) = ls := by
        intro ls; induction ls with | nil => rfl | cons _ _ ihf => simp [ihf]
      rw [hf, List.length_range]
    have hbij := xorRange_eq_filtered_of_inj
      (fun t => iter F t 0 % 2 ^ d) (fun _ => true)
      (fun y => xor ((evalPoly [P] y).testBit d) (((y ^^^ evalPoly [P] y) % 2 ^ d + c).testBit d))
      horb_in horb_inj hcnt
    rw [hbij]
    simp only [↓reduceIte, evalPoly, Nat.xor_zero]
    rw [xorRange_xor, htap_sum]
    have hcarry : xorRange (2 ^ d) (fun y => ((y ^^^ evalTap P y) % 2 ^ d + c).testBit d) = true := by
      have hcongr : ∀ y < 2 ^ d, ((y ^^^ evalTap P y) % 2 ^ d + c).testBit d = (y + c).testBit d := by
        intro y hy
        have hy_eq : (y ^^^ evalTap P y) % 2 ^ d = y := by
          rw [← Nat.mod_eq_of_lt hy, mod_two_pow_eq_iff]; intro i hi
          rw [Nat.testBit_xor, hbelow i hi, bxor_false, Nat.testBit_mod_two_pow]
          simp [hi]
        rw [hy_eq]
      rw [xorRange_congr hcongr, carry_xorRange_parity hd c, hc]; rfl
    rw [hcarry]; rfl
  have hsplit := exactPeriod_lift_split hbsi hEd hhol_false
  simp only [Nat.zero_xor] at hsplit
  exact ⟨hsingle_le, hsplit⟩

-- ============================================================================
-- PART VI: KERNEL-CHECKED NON-VACUITY WITNESSES & SHARPNESS COUNTEREXAMPLES
-- ============================================================================

/-- Non-Vacuity Witness 1: Nonlinear quadratic AND feedback `N(x) = (x <<< 2) &&& (x <<< 3)`
    genuinely satisfies `TwoDelayed N` AND the finite-slice parity gate `(N 0).testBit 2 = (N 1).testBit 2`,
    instantiating Theorem 2a for ALL `w ≥ 2` and `c = 1, 5, 9, ...` and Theorem 2b for `c = 1`! -/
def N_quad (x : Nat) : Nat := (x <<< 2) &&& (x <<< 3)

theorem N_quad_twoDelayed : TwoDelayed N_quad := by
  refine ⟨fun x => ⟨?_, ?_⟩, ?_⟩
  · simp [N_quad]
  · simp [N_quad, Nat.testBit_and, Nat.testBit_shiftLeft]
  · intro w x hw
    simp only [N_quad, Nat.testBit_and, Nat.testBit_shiftLeft]
    by_cases h3 : 3 ≤ w
    · have h2 : 2 ≤ w := by omega
      simp only [h2, h3, decide_true, Bool.true_and]
      rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
      simp [show w - 2 < w - 1 by omega, show w - 3 < w - 1 by omega]
    · simp [h3]

theorem witness_thm2a_N_quad_c5 (w : Nat) (hw : w ≥ 2) (x : Nat) (hx : x.testBit 1 = false) :
    ExactPeriod (hybridCarryNLFSR N_quad 5) w x (2 ^ (w - 1)) :=
  theorem2a_carry_pump_universal_giant_cycle N_quad_twoDelayed rfl (by decide) w hw x hx

theorem witness_thm2b_N_quad_barrier (x : Nat) (hx : x.testBit 1 = true) :
    (hybridCarryNLFSR N_quad 1 x).testBit 1 = true ∧
    hybridCarryNLFSR N_quad 1 x / 4 = (x ^^^ (x <<< 1) ^^^ N_quad x) / 4 :=
  theorem2b_carry_barrier_hermetic N_quad_twoDelayed x hx

/-- Non-Vacuity Witness 2: Mixed linear + quadratic + cubic non-prefix Hybrid XOR-AND-Carry NLFSR
    `M = [[2], [1, 3], [1, 2, 4]]` with `c = 3` is De Bruijn complete for ALL `w ≥ 1`! -/
def M_mixed : List (List Nat) := [[2], [1, 3], [1, 2, 4]]

theorem witness_thm3a_M_mixed (w : Nat) (hw : w ≥ 1) :
    SingleCycle (hybridTapNLFSR M_mixed 3) w := by
  apply theorem3a_nonprefix_hybrid_nlfsr_debruijn _ (by decide) w hw
  intro T hT
  simp only [M_mixed, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl
  · exact ⟨by decide, by decide, 1, by decide, ⟨2, by decide, by decide⟩, by decide⟩
  · exact ⟨by decide, by decide, 2, by decide, ⟨3, by decide, by decide⟩, by decide⟩
  · exact ⟨by decide, by decide, 3, by decide, ⟨4, by decide, by decide⟩, by decide⟩

/-- Sharpness Counterexample 1: Breaking the parity gate `(N 0).testBit 2 = (N 1).testBit 2`
    with 2-delayed `N_bad_gate(x) = (x <<< 2) ||| (x <<< 3)` immediately splits sector `x_1 = 0`
    at `w = 3` into period `2 ≠ 4`! -/
def N_bad_gate (x : Nat) : Nat := (x <<< 2) ||| (x <<< 3)

theorem sharpness_counterexample1_parity_gate :
    TwoDelayed N_bad_gate ∧
    (N_bad_gate 0).testBit 2 ≠ (N_bad_gate 1).testBit 2 ∧
    ExactPeriod (hybridCarryNLFSR N_bad_gate 1) 3 0 2 ∧
    ¬ ExactPeriod (hybridCarryNLFSR N_bad_gate 1) 3 0 4 := by
  refine ⟨⟨fun x => ⟨by simp [N_bad_gate],
                      by simp [N_bad_gate, Nat.testBit_or, Nat.testBit_shiftLeft]⟩, ?_⟩,
          by decide, exactPeriod_of_check (by decide), ?_⟩
  · intro w x hw
    simp only [N_bad_gate, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases h3 : 3 ≤ w
    · simp only [hw, h3, decide_true, Bool.true_and]
      rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
      simp [show w - 2 < w - 1 by omega, show w - 3 < w - 1 by omega]
    · simp only [hw, h3, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.or_false]
      rw [Nat.testBit_mod_two_pow]; simp [show w - 2 < w - 1 by omega]
  · intro h4
    exact h4.2.2 2 (by omega) (by omega) (by decide)

/-- Sharpness Counterexample 2: Breaking 2-delay with 1-delayed `N_bad_delay(x) = (x <<< 1) &&& (x <<< 3)`
    (which STILL satisfies the parity gate!) splits sector `x_1 = 0` at `w = 4` into period `4 ≠ 8`! -/
def N_bad_delay (x : Nat) : Nat := (x <<< 1) &&& (x <<< 3)

theorem sharpness_counterexample2_two_delay :
    (N_bad_delay 0).testBit 2 = (N_bad_delay 1).testBit 2 ∧
    ExactPeriod (hybridCarryNLFSR N_bad_delay 1) 4 0 4 ∧
    ¬ ExactPeriod (hybridCarryNLFSR N_bad_delay 1) 4 0 8 := by
  refine ⟨by decide, exactPeriod_of_check (by decide), ?_⟩
  intro h8
  exact h8.2.2 4 (by omega) (by omega) (by decide)

/-- Sharpness Counterexample 3: Breaking `c % 4 = 1` with `c = 3` splits `x_1 = 0` at `w = 4` into period `4 ≠ 8`! -/
theorem sharpness_counterexample3_c_mod4 :
    ExactPeriod (hybridCarryNLFSR (fun _ => 0) 3) 4 0 4 ∧
    ¬ ExactPeriod (hybridCarryNLFSR (fun _ => 0) 3) 4 0 8 := by
  refine ⟨exactPeriod_of_check (by decide), ?_⟩
  intro h8
  exact h8.2.2 4 (by omega) (by omega) (by decide)

/-- Sharpness Counterexample 4: Breaking `c = 1` with `c = 5` leaks a carry across bit 1 on `x = 2` (`x.testBit 1 = true`)! -/
theorem sharpness_counterexample4_carry_leak :
    (2 : Nat).testBit 1 = true ∧
    hybridCarryNLFSR (fun _ => 0) 5 2 / 4 ≠ (2 ^^^ (2 <<< 1) ^^^ 0) / 4 := by
  decide

/-- Sharpness Counterexample 5: Changing `+ 1` to `+ 3` in `H111` splits `w = 4` into period `4 ≠ 8`! -/
def H113 (x : Nat) : Nat := x + 2 * (x &&& (x <<< 1)) + 3

theorem sharpness_counterexample5_H113 :
    ExactPeriod H113 4 0 4 ∧ ¬ ExactPeriod H113 4 0 8 := by
  refine ⟨exactPeriod_of_check (by decide), ?_⟩
  intro h8
  exact h8.2.2 4 (by omega) (by omega) (by decide)

/-- Kernel-checked negative mutation tests on `checkLasso` (adversarial certificate integrity):
    1. Empty cycle rejected;
    2. Broken loop-back rejected;
    3. Corrupted state mask (wrong holonomy / wrong transition) rejected;
    4. Cross-sector certificate swap (`sector1` cert on `sector0` initial vector) rejected. -/
theorem neg_mut1_empty_cyc :
    checkLasso T_H111 (cylinderVec T_H111 (fun y => !y.testBit 2) 3 3) { pre := [12], cyc := [] } = false := by
  decide

theorem neg_mut2_broken_loop :
    checkLasso T_H111 (cylinderVec T_H111 (fun y => !y.testBit 2) 3 3) { pre := [], cyc := [12, 48] } = false := by
  decide

theorem neg_mut3_corrupted_mask :
    checkLasso T_K (cylinderVec T_K (fun _ => true) 1 1) { pre := [33, 153, 243, 48], cyc := [193] } = false := by
  decide

theorem neg_mut4_cross_sector_swap :
    checkLasso T_H111 (cylinderVec T_H111 (fun y => !y.testBit 2) 3 3) cert_H111_sector1 = false := by
  decide

-- ============================================================================
-- PART VII: KERNEL AXIOM AUDIT (`#print axioms`)
-- ============================================================================

end DynSil12
