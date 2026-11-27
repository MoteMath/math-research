/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CarryPrefixThresholdMonoid.Defs

/-!
# Theorems (`carry-prefix-threshold-monoid`)

Full proofs of the headline infinite theorems of Carry-lookahead prefix monoid with the threshold-step semigroup.
-/

namespace SiliconCarryMonoid

theorem ediv_emod_unique {a m q r : Int} (hm : 0 < m)
    (heq : a = m * q + r) (hr0 : 0 ≤ r) (hrm : r < m) :
    a / m = q ∧ a % m = r := by
  have hdiv : m * (a / m) + a % m = a := Int.mul_ediv_add_emod a m
  have hrem0 : 0 ≤ a % m := Int.emod_nonneg a (by omega)
  have hremm : a % m < m := Int.emod_lt_of_pos a hm
  have hdiff : m * (a / m - q) = r - a % m := by
    have : m * (a / m) - m * q = r - a % m := by omega
    rw [Int.mul_sub]
    exact this
  have hq : a / m = q := by
    by_cases hgt : a / m > q
    · have h1 : 1 ≤ a / m - q := by omega
      have h2 : m * 1 ≤ m * (a / m - q) := Int.mul_le_mul_of_nonneg_left h1 (by omega)
      omega
    · by_cases hlt : a / m < q
      · have h1 : a / m - q ≤ -1 := by omega
        have h2 : m * (a / m - q) ≤ m * (-1) := Int.mul_le_mul_of_nonneg_left h1 (by omega)
        have h3 : m * (-1) = -m := by omega
        omega
      · omega
  refine ⟨hq, ?_⟩
  rw [hq] at hdiv
  omega

theorem ediv_ediv_add {m₁ m₂ : Int} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (c s₁ s₂ : Int) :
    ((c + s₁) / m₁ + s₂) / m₂ = (c + s₁ + m₁ * s₂) / (m₁ * m₂) := by
  let q₁ := (c + s₁) / m₁
  let r₁ := (c + s₁) % m₁
  let q₂ := (q₁ + s₂) / m₂
  let r₂ := (q₁ + s₂) % m₂
  have h1 : m₁ * q₁ + r₁ = c + s₁ := Int.mul_ediv_add_emod (c + s₁) m₁
  have h2 : m₂ * q₂ + r₂ = q₁ + s₂ := Int.mul_ediv_add_emod (q₁ + s₂) m₂
  have hr₁0 : 0 ≤ r₁ := Int.emod_nonneg _ (by omega)
  have hr₁m : r₁ < m₁ := Int.emod_lt_of_pos _ hm₁
  have hr₂0 : 0 ≤ r₂ := Int.emod_nonneg _ (by omega)
  have hr₂m : r₂ < m₂ := Int.emod_lt_of_pos _ hm₂
  have hprod_pos : 0 < m₁ * m₂ := Int.mul_pos hm₁ hm₂
  have heq : c + s₁ + m₁ * s₂ = (m₁ * m₂) * q₂ + (m₁ * r₂ + r₁) := by
    calc c + s₁ + m₁ * s₂
        = (m₁ * q₁ + r₁) + m₁ * s₂ := by rw [← h1]
      _ = m₁ * (q₁ + s₂) + r₁ := by rw [Int.mul_add]; omega
      _ = m₁ * (m₂ * q₂ + r₂) + r₁ := by rw [← h2]
      _ = (m₁ * m₂) * q₂ + (m₁ * r₂ + r₁) := by
          rw [Int.mul_add, Int.mul_assoc]; omega
  have hr_nonneg : 0 ≤ m₁ * r₂ + r₁ := by
    have : 0 ≤ m₁ * r₂ := Int.mul_nonneg (by omega) hr₂0
    omega
  have hr_lt : m₁ * r₂ + r₁ < m₁ * m₂ := by
    have hstep : m₁ * r₂ + m₁ = m₁ * (r₂ + 1) := by rw [Int.mul_add, Int.mul_one]
    have hle : m₁ * (r₂ + 1) ≤ m₁ * m₂ :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  exact (ediv_emod_unique hprod_pos heq hr_nonneg hr_lt).1.symm

-- ============================================================================
-- 1. Universal Associative Prefix-Tree Engine
-- ============================================================================

namespace PrefixTree

theorem width_eq_fringe_length (t : PrefixTree α) : t.width = t.fringe.length := by
  induction t with
  | leaf _ => rfl
  | node lo hi ihlo ihhi =>
    simp [width, fringe, List.length_append, ihlo, ihhi]

theorem width_pos (t : PrefixTree α) : 0 < t.width := by
  induction t with
  | leaf _ => exact Nat.one_pos
  | node lo _ ihlo => simp [width]; omega

theorem rippleNonempty_append [PrefixSemigroup M] (x : M) (xs : List M) (y : M) (ys : List M) :
    rippleNonempty x (xs ++ y :: ys) =
      PrefixSemigroup.mul (rippleNonempty y ys) (rippleNonempty x xs) := by
  induction xs generalizing x with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.cons_append, rippleNonempty]
    rw [ih z, PrefixSemigroup.mul_assoc]

theorem rippleMonoid_append [PrefixMonoid M] (xs ys : List M) :
    rippleMonoid (xs ++ ys) = PrefixSemigroup.mul (rippleMonoid ys) (rippleMonoid xs) := by
  induction xs with
  | nil => simp [rippleMonoid, PrefixMonoid.mul_one]
  | cons x xs ih =>
    simp only [List.cons_append, rippleMonoid]
    rw [ih, PrefixSemigroup.mul_assoc]

theorem eval_eq_rippleMonoid [PrefixMonoid M] (enc : α → M) (t : PrefixTree α) :
    t.eval enc = rippleMonoid (t.fringe.map enc) := by
  induction t with
  | leaf a => simp [eval, fringe, rippleMonoid, PrefixMonoid.one_mul]
  | node lo hi ihlo ihhi =>
    simp only [eval, fringe, List.map_append]
    rw [rippleMonoid_append, ihlo, ihhi]

theorem fringe_nonempty (t : PrefixTree α) : ∃ x xs, t.fringe = x :: xs := by
  induction t with
  | leaf a => exact ⟨a, [], rfl⟩
  | node lo hi ihlo _ =>
    rcases ihlo with ⟨x, xs, hlo⟩
    exact ⟨x, xs ++ hi.fringe, by simp [fringe, hlo]⟩

theorem eval_eq_rippleNonempty [PrefixSemigroup M] (enc : α → M) (t : PrefixTree α) :
    ∀ x xs, t.fringe = x :: xs → t.eval enc = rippleNonempty (enc x) (xs.map enc) := by
  induction t with
  | leaf a =>
    intro x xs h
    simp only [fringe, List.cons.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | node lo hi ihlo ihhi =>
    intro x xs h
    rcases lo.fringe_nonempty with ⟨x₁, xs₁, hlo⟩
    rcases hi.fringe_nonempty with ⟨x₂, xs₂, hhi⟩
    simp only [fringe, hlo, hhi, List.cons_append, List.cons.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp only [eval, List.map_append, List.map_cons]
    rw [rippleNonempty_append, ihlo x₁ xs₁ hlo, ihhi x₂ xs₂ hhi]

/-- **Theorem 1 (Associative-Tree Universality):**
Any two prefix trees with the same fringe evaluate identically in ANY associative semigroup. -/
theorem associative_tree_universality [PrefixSemigroup M] (enc : α → M)
    (t₁ t₂ : PrefixTree α) (h : t₁.fringe = t₂.fringe) :
    t₁.eval enc = t₂.eval enc := by
  rcases t₁.fringe_nonempty with ⟨x, xs, h₁⟩
  have h₂ : t₂.fringe = x :: xs := h.symm.trans h₁
  rw [eval_eq_rippleNonempty enc t₁ x xs h₁, eval_eq_rippleNonempty enc t₂ x xs h₂]

/-- **Theorem 1b (Stateful Carry-Action Universality):**
For any semigroup action matching per-slice carry transitions, evaluating ANY prefix tree
topology produces the exact same carry-out as sequential ripple-carry for all widths `w ≥ 1`. -/
theorem action_universality [PrefixSemigroup M] (enc : α → M)
    (act : M → S → S) (step : α → S → S)
    (hact_mul : ∀ hi lo c, act (PrefixSemigroup.mul hi lo) c = act hi (act lo c))
    (hact_enc : ∀ a c, act (enc a) c = step a c)
    (t : PrefixTree α) (c : S) :
    act (t.eval enc) c = t.fringe.foldl (fun s a => step a s) c := by
  induction t generalizing c with
  | leaf a => simp [eval, fringe, hact_enc]
  | node lo hi ihlo ihhi =>
    simp only [eval, fringe, List.foldl_append]
    rw [hact_mul, ihlo, ihhi]

end PrefixTree

namespace DivElem

theorem one_act (c : Int) : one.act c = c := by
  simp only [one, act, Int.add_zero]
  exact Int.ediv_one c

theorem comp_act (hi lo : DivElem) (c : Int) :
    (hi.comp lo).act c = hi.act (lo.act c) := by
  simp only [comp, act]
  have hm₁ : (0 : Int) < (lo.mod : Int) := by have := lo.mod_pos; omega
  have hm₂ : (0 : Int) < (hi.mod : Int) := by have := hi.mod_pos; omega
  rw [natCast_mul_int]
  have hadd : c + (lo.sum + (lo.mod : Int) * hi.sum) = c + lo.sum + (lo.mod : Int) * hi.sum := by omega
  rw [hadd]
  exact (ediv_ediv_add hm₁ hm₂ c lo.sum hi.sum).symm

theorem preserves_comp {L U : Int} {hi lo : DivElem}
    (hhi : hi.Preserves L U) (hlo : lo.Preserves L U) :
    (hi.comp lo).Preserves L U := by
  intro c hcL hcU
  rw [comp_act]
  have h1 := hlo c hcL hcU
  exact hhi (lo.act c) h1.1 h1.2

/-- Exact signed multi-input base-`b` carry-invariant theorem:
With `p` added operands and `q` subtracted operands (`p + q ≥ 1`), any column sum
`s ∈ [-q(b-1), p(b-1)]` preserves the tight carry-borrow interval `[-q, p - 1]`. -/
theorem signed_multi_input_slice_preserves (b p q : Nat) (hb : 2 ≤ b) (s : Int)
    (hsL : -((q : Int) * ((b : Int) - 1)) ≤ s)
    (hsU : s ≤ (p : Int) * ((b : Int) - 1)) :
    Preserves (-(q : Int)) ((p : Int) - 1) ⟨b, by omega, s⟩ := by
  intro c hcL hcU
  simp only [act]
  have hb_pos : (0 : Int) < (b : Int) := by omega
  let k := (c + s) / (b : Int)
  have hdiv : (b : Int) * k + (c + s) % (b : Int) = c + s := Int.mul_ediv_add_emod (c + s) (b : Int)
  have hrem0 : 0 ≤ (c + s) % (b : Int) := Int.emod_nonneg _ (by omega)
  have hremm : (c + s) % (b : Int) < (b : Int) := Int.emod_lt_of_pos _ hb_pos
  constructor
  · by_cases hlt : -(q : Int) ≤ k
    · exact hlt
    · have hk : k ≤ -(q : Int) - 1 := by omega
      have hmul : (b : Int) * k ≤ (b : Int) * (-(q : Int) - 1) :=
        Int.mul_le_mul_of_nonneg_left hk (by omega)
      have hexp : (b : Int) * (-(q : Int) - 1) = -((q : Int) * (b : Int)) - (b : Int) := by
        rw [Int.mul_sub, Int.mul_neg, Int.mul_one, Int.mul_comm (b : Int) (q : Int)]
      have hbound : -((q : Int) * (b : Int)) ≤ c + s := by
        have : (q : Int) * ((b : Int) - 1) = (q : Int) * (b : Int) - (q : Int) := by
          rw [Int.mul_sub, Int.mul_one]
        omega
      omega
  · by_cases hgt : k ≤ (p : Int) - 1
    · exact hgt
    · have hk : (p : Int) ≤ k := by omega
      have hmul : (b : Int) * (p : Int) ≤ (b : Int) * k :=
        Int.mul_le_mul_of_nonneg_left hk (by omega)
      have hcomm : (b : Int) * (p : Int) = (p : Int) * (b : Int) := Int.mul_comm _ _
      have hbound : c + s ≤ (p : Int) * (b : Int) - 1 := by
        have : (p : Int) * ((b : Int) - 1) = (p : Int) * (b : Int) - (p : Int) := by
          rw [Int.mul_sub, Int.mul_one]
        omega
      omega

end DivElem

namespace ThreshElem

/-- **Theorem 3d (Universal Aperiodicity / 2-Step Idempotence: `e³ = e²`).**
In Krohn-Rhodes semigroup theory, `T` is an aperiodic (H-trivial / star-free) semigroup
of index ≤ 2. -/
theorem aperiodic (e : ThreshElem) : e.comp (e.comp e) = e.comp e := by
  cases e with
  | const q => rfl
  | step q t =>
    by_cases h1 : q ≥ t
    · have h1' : q + 1 ≥ t := by omega
      simp [comp, h1, h1']
    · by_cases h2 : q + 1 < t
      · simp [comp, h1, h2]
      · simp [comp, h1, h2]

/-- **Theorem 3e (Exact 2-Step Absorption Criterion for Squaring):**
`e²` is constant iff `e` is not of the self-resonant form `step q (q + 1)`. -/
theorem sq_isConst_iff (e : ThreshElem) :
    (e.comp e).isConst = true ↔ ¬ (∃ q, e = .step q (q + 1)) := by
  cases e with
  | const q => simp [comp, isConst]
  | step q t =>
    by_cases h1 : q ≥ t
    · simp only [comp, h1, ↓reduceIte, isConst]
      constructor
      · intro _ ⟨q', hq'⟩; injection hq' with ha hb; omega
      · intro _; trivial
    · by_cases h2 : q + 1 < t
      · simp only [comp, h1, h2, ↓reduceIte, isConst]
        constructor
        · intro _ ⟨q', hq'⟩; injection hq' with ha hb; omega
        · intro _; trivial
      · have heq : t = q + 1 := by omega
        subst heq
        have hn1 : ¬ (q ≥ q + 1) := by omega
        have hn2 : ¬ (q + 1 < q + 1) := by omega
        simp [comp, hn1, hn2, isConst]

/-- **Theorem 3f (`T_[L, U]` is Closed under Composition).** -/
theorem inBounds_comp {L U : Int} {hi lo : ThreshElem}
    (hhi : hi.inBounds L U) (hlo : lo.inBounds L U) :
    (hi.comp lo).inBounds L U := by
  cases hi with
  | const q₂ => exact hhi
  | step q₂ t₂ =>
    rcases hhi with ⟨hq₂L, hq₂U, ht₂L, ht₂U⟩
    cases lo with
    | const q₁ =>
      simp only [comp, inBounds]
      by_cases h : q₁ ≥ t₂ <;> simp [h] <;> omega
    | step q₁ t₁ =>
      rcases hlo with ⟨hq₁L, hq₁U, ht₁L, ht₁U⟩
      simp only [comp]
      by_cases h1 : q₁ ≥ t₂
      · simp only [h1, ↓reduceIte, inBounds]; omega
      · by_cases h2 : q₁ + 1 < t₂
        · simp only [h1, h2, ↓reduceIte, inBounds]; omega
        · simp only [h1, h2, ↓reduceIte, inBounds]; exact ⟨hq₂L, hq₂U, ht₁L, ht₁U⟩

/-- **Theorem 3g (Injectivity of `eval` even when restricted ONLY to `[L, U]`).** -/
theorem inBounds_eval_injective {L U : Int} (hLU : L ≤ U) {e₁ e₂ : ThreshElem}
    (h₁ : e₁.inBounds L U) (h₂ : e₂.inBounds L U)
    (heq : ∀ c : Int, L ≤ c → c ≤ U → e₁.eval c = e₂.eval c) :
    e₁ = e₂ := by
  cases e₁ with
  | const q₁ =>
    cases e₂ with
    | const q₂ =>
      have hL := heq L (Int.le_refl L) hLU
      simp [eval] at hL
      rw [hL]
    | step q₂ t₂ =>
      rcases h₂ with ⟨_, _, ht₂L, ht₂U⟩
      have hlo := heq (t₂ - 1) (by omega) (by omega)
      have hhi := heq t₂ (by omega) ht₂U
      simp [eval] at hlo hhi
      omega
  | step q₁ t₁ =>
    rcases h₁ with ⟨_, _, ht₁L, ht₁U⟩
    cases e₂ with
    | const q₂ =>
      have hlo := heq (t₁ - 1) (by omega) (by omega)
      have hhi := heq t₁ (by omega) ht₁U
      simp [eval] at hlo hhi
      omega
    | step q₂ t₂ =>
      rcases h₂ with ⟨_, _, ht₂L, ht₂U⟩
      have hL := heq L (Int.le_refl L) hLU
      simp only [eval] at hL
      have h1 : ¬ (L ≥ t₁) := by omega
      have h2 : ¬ (L ≥ t₂) := by omega
      simp only [h1, h2, ↓reduceIte] at hL
      have ht₁ := heq t₁ (by omega) ht₁U
      have ht₂ := heq t₂ (by omega) ht₂U
      simp only [eval] at ht₁ ht₂
      have hge1 : t₁ ≥ t₁ := by omega
      have hge2 : t₂ ≥ t₂ := by omega
      simp only [hge1, hge2, ↓reduceIte] at ht₁ ht₂
      have ht : t₁ = t₂ := by
        by_cases hlt : t₁ < t₂
        · have : ¬ (t₁ ≥ t₂) := by omega
          simp only [this, ↓reduceIte] at ht₁
          omega
        · by_cases hgt : t₂ < t₁
          · have : ¬ (t₂ ≥ t₁) := by omega
            simp only [this, ↓reduceIte] at ht₂
            omega
          · omega
      rw [hL, ht]

/-- **Theorem 3h (Exact Finite-State Cardinality `|T_[L, U]| = N² - N + 1`):**
For `N ≥ 1` carry states (e.g. `N = k` for `k`-input signed/unsigned addition),
`T_[L, L + N - 1]` has exact cardinality `N² - N + 1`, with zero duplicates and complete
coverage of `inBounds`. -/
theorem enumBounded_length (L : Int) (N : Nat) (hN : 1 ≤ N) :
    (enumBounded L N).length = N * N - N + 1 := by
  have hflat : ∀ (k m : Nat) (f : Nat → List ThreshElem),
      (∀ i, (f i).length = m) → ((List.range k).flatMap f).length = k * m := by
    intro k m f hf
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append, ih]
      simp [hf, Nat.succ_mul]
  simp only [enumBounded, List.length_append, List.length_map, List.length_range]
  rw [hflat (N - 1) (N - 1) _ (fun i => by simp)]
  cases N with
  | zero => omega
  | succ m =>
    simp only [Nat.add_sub_cancel]
    have h1 : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by
      rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]; omega
    omega

theorem enumBounded_complete (L : Int) (N : Nat) (hN : 1 ≤ N) (e : ThreshElem) :
    e ∈ enumBounded L N ↔ e.inBounds L (L + (N : Int) - 1) := by
  simp only [enumBounded, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap]
  cases e with
  | const q =>
    simp only [inBounds, ThreshElem.const.injEq, reduceCtorEq, and_false, exists_false, or_false]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · intro ⟨hL, hU⟩
      refine ⟨(q - L).toNat, ?_, ?_⟩ <;> omega
  | step q t =>
    simp only [inBounds, reduceCtorEq, and_false, exists_false, false_or, ThreshElem.step.injEq]
    constructor
    · rintro ⟨i, hi, j, hj, rfl, rfl⟩; omega
    · intro ⟨hqL, hqU, htL, htU⟩
      refine ⟨(q - L).toNat, ?_, (t - L - 1).toNat, ?_, ?_, ?_⟩ <;> omega

theorem enumBounded_nodup (L : Int) (N : Nat) : (enumBounded L N).Nodup := by
  have nodup_range : ∀ k : Nat, (List.range k).Nodup := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.nodup_append]
      refine ⟨ih, by simp [List.nodup_cons], ?_⟩
      intro a ha b hb
      simp only [List.mem_range] at ha
      simp only [List.mem_singleton] at hb
      omega
  have nodup_map_inj : ∀ {α β : Type} (f : α → β) (l : List α),
      (∀ x y, f x = f y → x = y) → l.Nodup → (l.map f).Nodup := by
    intro α β f l hinj hl
    induction l with
    | nil => simp
    | cons a as ih =>
      simp only [List.nodup_cons, List.map_cons, List.mem_map] at hl ⊢
      refine ⟨?_, ih hl.2⟩
      rintro ⟨b, hb, hfab⟩
      have := hinj b a hfab
      subst this
      exact hl.1 hb
  simp only [enumBounded]
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · apply nodup_map_inj (fun i : Nat => ThreshElem.const (L + (i : Int))) _
      (fun x y h => by injection h with h1; omega) (nodup_range N)
  · have hflat_nodup : ∀ k : Nat,
        ((List.range k).flatMap (fun i : Nat =>
          (List.range (N - 1)).map (fun j : Nat => ThreshElem.step (L + (i : Int)) (L + 1 + (j : Int))))).Nodup := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [List.range_succ, List.flatMap_append, List.nodup_append]
        refine ⟨ih, ?_, ?_⟩
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          apply nodup_map_inj (fun j : Nat => ThreshElem.step (L + (k : Int)) (L + 1 + (j : Int))) _
            (fun x y h => by injection h with _ h2; omega) (nodup_range (N - 1))
        · intro a ha b hb
          simp only [List.mem_flatMap, List.mem_range, List.mem_map] at ha hb
          rcases ha with ⟨i₁, hi₁, j₁, _, rfl⟩
          rcases hb with ⟨i₂, hi₂, j₂, _, rfl⟩
          simp only [List.mem_singleton] at hi₂
          intro heq
          injection heq with hq _
          omega
    exact hflat_nodup (N - 1)
  · intro a ha b hb heq
    simp only [List.mem_map] at ha
    simp only [List.mem_flatMap, List.mem_map] at hb
    rcases ha with ⟨_, _, rfl⟩
    rcases hb with ⟨_, _, _, _, rfl⟩
    exact ThreshElem.noConfusion heq

theorem embedClassicalGP_sound (g p : Bool) (c : Bool) :
    (embedClassicalGP g p).eval (if c then 1 else 0) = if (g || (p && c)) then 1 else 0 := by
  cases g <;> cases p <;> cases c <;> rfl

theorem embedSignedBorrow_sound (b p : Bool) (c : Bool) :
    (embedSignedBorrow b p).eval (if c then -1 else 0) = if (b || (p && c)) then -1 else 0 := by
  cases b <;> cases p <;> cases c <;> rfl

end ThreshElem

/-- **Theorem 4a (Super-Critical Collapse Soundness — `∀ M ≥ U - L`):**
Whenever the block modulus `M ≥ U - L`, the exact carry transfer function
`c ↦ ⌊(c + S) / M⌋` on `[L, U]` collapses with zero error into `ThreshElem`. -/
theorem collapse_sound (L U : Int) (d : DivElem) (hM : U - L ≤ (d.mod : Int))
    (c : Int) (hcL : L ≤ c) (hcU : c ≤ U) :
    (collapse L U d).eval c = d.act c := by
  unfold collapse DivElem.act
  dsimp only
  have hm : (0 : Int) < (d.mod : Int) := by have := d.mod_pos; omega
  have hdiv : (d.mod : Int) * ((L + d.sum) / (d.mod : Int)) + (L + d.sum) % (d.mod : Int) = L + d.sum :=
    Int.mul_ediv_add_emod (L + d.sum) (d.mod : Int)
  have hr0 : 0 ≤ (L + d.sum) % (d.mod : Int) := Int.emod_nonneg _ (by omega)
  have hrm : (L + d.sum) % (d.mod : Int) < (d.mod : Int) := Int.emod_lt_of_pos _ hm
  by_cases habs : (L + d.sum) % (d.mod : Int) + (U - L) < (d.mod : Int)
  · simp only [habs, ↓reduceIte, ThreshElem.eval]
    have heq : c + d.sum = (d.mod : Int) * ((L + d.sum) / (d.mod : Int)) + ((L + d.sum) % (d.mod : Int) + (c - L)) := by omega
    exact (ediv_emod_unique hm heq (by omega) (by omega)).1.symm
  · simp only [habs, ↓reduceIte, ThreshElem.eval]
    by_cases hge : c ≥ L + (d.mod : Int) - (L + d.sum) % (d.mod : Int)
    · simp only [hge, ↓reduceIte]
      have heq : c + d.sum = (d.mod : Int) * ((L + d.sum) / (d.mod : Int) + 1) +
          ((L + d.sum) % (d.mod : Int) + (c - L) - (d.mod : Int)) := by
        rw [Int.mul_add, Int.mul_one]; omega
      exact (ediv_emod_unique hm heq (by omega) (by omega)).1.symm
    · simp only [hge, ↓reduceIte]
      have heq : c + d.sum = (d.mod : Int) * ((L + d.sum) / (d.mod : Int)) + ((L + d.sum) % (d.mod : Int) + (c - L)) := by omega
      exact (ediv_emod_unique hm heq (by omega) (by omega)).1.symm

/-- **Theorem 4b (Collapse Preserves `T_[L, U]` Bounds):**
For any invariant-preserving super-critical block, `collapse` lands inside `T_[L, U]`. -/
theorem collapse_inBounds (L U : Int) (hLU : L ≤ U) (d : DivElem)
    (hM : U - L ≤ (d.mod : Int)) (hpres : d.Preserves L U) :
    (collapse L U d).inBounds L U := by
  have hactL := collapse_sound L U d hM L (Int.le_refl L) hLU
  have hactU := collapse_sound L U d hM U hLU (Int.le_refl U)
  have hpL := hpres L (Int.le_refl L) hLU
  have hpU := hpres U hLU (Int.le_refl U)
  unfold collapse at hactL hactU ⊢
  dsimp only at hactL hactU ⊢
  have hm : (0 : Int) < (d.mod : Int) := by have := d.mod_pos; omega
  have hr0 : 0 ≤ (L + d.sum) % (d.mod : Int) := Int.emod_nonneg _ (by omega)
  have hrm : (L + d.sum) % (d.mod : Int) < (d.mod : Int) := Int.emod_lt_of_pos _ hm
  by_cases habs : (L + d.sum) % (d.mod : Int) + (U - L) < (d.mod : Int)
  · simp only [habs, ↓reduceIte, ThreshElem.eval] at hactL
    simp only [habs, ↓reduceIte, ThreshElem.inBounds]
    omega
  · simp only [habs, ↓reduceIte, ThreshElem.eval] at hactL hactU
    have hL_not : ¬ (L ≥ L + (d.mod : Int) - (L + d.sum) % (d.mod : Int)) := by omega
    have hU_ge : U ≥ L + (d.mod : Int) - (L + d.sum) % (d.mod : Int) := by omega
    simp only [hL_not, ↓reduceIte] at hactL
    simp only [hU_ge, ↓reduceIte] at hactU
    simp only [habs, ↓reduceIte, ThreshElem.inBounds]
    omega

/-- **Theorem 4c (Exact Semigroup Homomorphism on Invariant Super-Blocks):**
Composing collapsed blocks in `T_[L, U]` equals collapsing the composite `DivElem`
on syntax itself (`=`), not merely up to extensionality! -/
theorem collapse_homomorphism (L U : Int) (hLU : L ≤ U) (hi lo : DivElem)
    (hMhi : U - L ≤ (hi.mod : Int)) (hMlo : U - L ≤ (lo.mod : Int))
    (hphi : hi.Preserves L U) (hplo : lo.Preserves L U) :
    collapse L U (hi.comp lo) = (collapse L U hi).comp (collapse L U lo) := by
  have hMcomp : U - L ≤ ((hi.comp lo).mod : Int) := by
    simp only [DivElem.comp]
    rw [natCast_mul_int]
    have h1 : (1 : Int) ≤ (hi.mod : Int) := by have := hi.mod_pos; omega
    have h2 : (lo.mod : Int) * 1 ≤ (lo.mod : Int) * (hi.mod : Int) :=
      Int.mul_le_mul_of_nonneg_left h1 (by omega)
    omega
  have hpcomp : (hi.comp lo).Preserves L U := DivElem.preserves_comp hphi hplo
  apply ThreshElem.inBounds_eval_injective hLU
    (collapse_inBounds L U hLU (hi.comp lo) hMcomp hpcomp)
    (ThreshElem.inBounds_comp
      (collapse_inBounds L U hLU hi hMhi hphi)
      (collapse_inBounds L U hLU lo hMlo hplo))
  intro c hcL hcU
  rw [collapse_sound L U (hi.comp lo) hMcomp c hcL hcU,
      DivElem.comp_act,
      ThreshElem.comp_eval,
      collapse_sound L U lo hMlo c hcL hcU]
  have hmid := hplo c hcL hcU
  rw [collapse_sound L U hi hMhi (lo.act c) hmid.1 hmid.2]

/-- **Theorem 4d (Infinite Parallel-Prefix Tree Synthesis Theorem):**
For ANY binary prefix tree `t` of ANY width `w ≥ 1` whose super-block leaves all have
`mod ≥ U - L` and preserve `[L, U]`, evaluating `t` in the finite `(N²-N+1)`-state
semigroup `T_[L, U]` computes the EXACT carry-out of the entire width-`W` circuit. -/
theorem collapse_tree_universality (L U : Int) (hLU : L ≤ U) (t : PrefixTree DivElem)
    (hleaves : ∀ d ∈ t.fringe, U - L ≤ (d.mod : Int) ∧ d.Preserves L U)
    (c : Int) (hcL : L ≤ c) (hcU : c ≤ U) :
    (t.eval (collapse L U)).eval c = (t.eval id).act c := by
  have hmain : ∀ tr : PrefixTree DivElem,
      (∀ d ∈ tr.fringe, U - L ≤ (d.mod : Int) ∧ d.Preserves L U) →
      tr.eval (collapse L U) = collapse L U (tr.eval id) ∧
      U - L ≤ ((tr.eval id).mod : Int) ∧ (tr.eval id).Preserves L U := by
    intro tr
    induction tr with
    | leaf d =>
      intro hl
      have hd := hl d (by simp [PrefixTree.fringe])
      exact ⟨rfl, hd.1, hd.2⟩
    | node lo hi ihlo ihhi =>
      intro hl
      have hlo := ihlo (fun d hd => hl d (by simp [PrefixTree.fringe, hd]))
      have hhi := ihhi (fun d hd => hl d (by simp [PrefixTree.fringe, hd]))
      rcases hlo with ⟨helo, hMlo, hplo⟩
      rcases hhi with ⟨hehi, hMhi, hphi⟩
      have hMcomp : U - L ≤ (((hi.eval id).comp (lo.eval id)).mod : Int) := by
        simp only [DivElem.comp]
        rw [natCast_mul_int]
        have h1 : (1 : Int) ≤ ((hi.eval id).mod : Int) := by have := (hi.eval id).mod_pos; omega
        have h2 : ((lo.eval id).mod : Int) * 1 ≤ ((lo.eval id).mod : Int) * ((hi.eval id).mod : Int) :=
          Int.mul_le_mul_of_nonneg_left h1 (by omega)
        omega
      refine ⟨?_, hMcomp, DivElem.preserves_comp hphi hplo⟩
      simp only [PrefixTree.eval, PrefixSemigroup.mul]
      rw [helo, hehi, ← collapse_homomorphism L U hLU (hi.eval id) (lo.eval id) hMhi hMlo hphi hplo]
  rcases hmain t hleaves with ⟨heq, hM, _⟩
  rw [heq]
  exact collapse_sound L U (t.eval id) hM c hcL hcU

/-- **Theorem 4e (Exact Sharpness Obstruction — `∀ M < U - L`):**
Whenever `M < U - L`, there exists a digit sum `S` whose carry-transfer function takes
3 distinct values `{0, 1, 2}` on `[L, U]`, making collapse into `ThreshElem` impossible. -/
theorem collapse_sharpness_obstruction (L U : Int) (M : Nat) (hMpos : 0 < M)
    (hsub : (M : Int) < U - L) :
    ∃ d : DivElem, d.mod = M ∧
      ¬ ∃ e : ThreshElem, ∀ c : Int, L ≤ c → c ≤ U → e.eval c = d.act c := by
  let d : DivElem := ⟨M, hMpos, (M : Int) - 1 - L⟩
  refine ⟨d, rfl, ?_⟩
  rintro ⟨e, he⟩
  have hm : (0 : Int) < (M : Int) := by omega
  have hv0 : d.act L = 0 := by
    simp only [d, DivElem.act]
    exact (ediv_emod_unique hm (q := 0) (r := (M : Int) - 1) (by omega) (by omega) (by omega)).1
  have hv1 : d.act (L + 1) = 1 := by
    simp only [d, DivElem.act]
    exact (ediv_emod_unique hm (q := 1) (r := 0) (by omega) (by omega) (by omega)).1
  have hv2 : d.act (L + (M : Int) + 1) = 2 := by
    simp only [d, DivElem.act]
    exact (ediv_emod_unique hm (q := 2) (r := 0) (by omega) (by omega) (by omega)).1
  have h0 := he L (by omega) (by omega)
  have h1 := he (L + 1) (by omega) (by omega)
  have h2 := he (L + (M : Int) + 1) (by omega) (by omega)
  rw [hv0] at h0
  rw [hv1] at h1
  rw [hv2] at h2
  cases e with
  | const q => simp [ThreshElem.eval] at h0 h1; omega
  | step q t =>
    simp only [ThreshElem.eval] at h0 h1 h2
    by_cases c0 : L ≥ t <;> by_cases c1 : L + 1 ≥ t <;> by_cases c2 : L + (M : Int) + 1 ≥ t
    all_goals simp only [c0, c1, c2, ↓reduceIte] at h0 h1 h2
    all_goals omega

/-- Sharpness Corollary: 4-input binary addition (`[0, 3]`) CANNOT collapse at width `w = 1`
(`M = 2 < 3`), and DOES collapse at width `w = 2` (`M = 4 ≥ 3`). -/
theorem four_input_binary_width_sharpness :
    (∃ d : DivElem, d.mod = 2 ∧
      ¬ ∃ e : ThreshElem, ∀ c : Int, 0 ≤ c → c ≤ 3 → e.eval c = d.act c) ∧
    (∀ S : Int, ∀ c : Int, 0 ≤ c → c ≤ 3 →
      (collapse 0 3 ⟨4, by omega, S⟩).eval c = (DivElem.mk 4 (by omega) S).act c) := by
  exact ⟨collapse_sharpness_obstruction 0 3 2 (by omega) (by omega),
         fun S c hc0 hc3 => collapse_sound 0 3 ⟨4, by omega, S⟩ (by simp) c hc0 hc3⟩

/-- **Theorem 4f (Sharpness Counterexample for Carry-Invariant Hypothesis):**
If block 1 violates `[0, 2]` (`S₁ = 6`), `collapse` fails to be a homomorphism (`lhs = 1 ≠ 2 = rhs`). -/
theorem invariant_violation_counterexample :
    let d₁ : DivElem := ⟨2, by omega, 6⟩
    let d₂ : DivElem := ⟨2, by omega, 0⟩
    ((collapse 0 2 d₂).comp (collapse 0 2 d₁)).eval 2 = 1 ∧
    (d₂.comp d₁).act 2 = 2 := by
  decide

-- ============================================================================
-- 5. Exact Infinite Carry-Absorption & Resonance-Lock Laws (∀ w ≥ 1)
-- ============================================================================

theorem rippleNonempty_step_iff (x : ThreshElem) (xs : List ThreshElem) :
    (∃ q t, PrefixTree.rippleNonempty x xs = .step q t) ↔ ResonantChain (x :: xs) := by
  induction xs generalizing x with
  | nil =>
    cases x with
    | const q => simp [PrefixTree.rippleNonempty, ResonantChain]
    | step q t => simp [PrefixTree.rippleNonempty, ResonantChain]
  | cons y ys ih =>
    cases x with
    | const q₁ =>
      simp only [PrefixTree.rippleNonempty, ResonantChain]
      constructor
      · rintro ⟨q, t, h⟩
        cases hrem : PrefixTree.rippleNonempty y ys with
        | const q₂ => simp [hrem, PrefixSemigroup.mul, ThreshElem.comp] at h
        | step q₂ t₂ => simp [hrem, PrefixSemigroup.mul, ThreshElem.comp] at h
      · intro hf; exact False.elim hf
    | step q₁ t₁ =>
      cases y with
      | const q₂ =>
        simp only [PrefixTree.rippleNonempty, ResonantChain]
        constructor
        · rintro ⟨q, t, h⟩
          have hnot : ¬ ∃ q' t', PrefixTree.rippleNonempty (.const q₂) ys = .step q' t' := by
            rw [ih (.const q₂)]
            cases ys <;> simp [ResonantChain]
          cases hrem : PrefixTree.rippleNonempty (.const q₂) ys with
          | const q' => simp [hrem, PrefixSemigroup.mul, ThreshElem.comp] at h
          | step q' t' => exact hnot ⟨q', t', hrem⟩
        · intro hf; exact False.elim hf
      | step q₂ t₂ =>
        have hhead : ∀ (q₀ t₀ : Int) (zs : List ThreshElem) (q' t' : Int),
            PrefixTree.rippleNonempty (.step q₀ t₀) zs = .step q' t' → t' = t₀ := by
          intro q₀ t₀ zs
          induction zs generalizing q₀ t₀ with
          | nil =>
            intro q' t' h
            simp only [PrefixTree.rippleNonempty, ThreshElem.step.injEq] at h
            exact h.2.symm
          | cons z zs' ihz =>
            intro q' t' h
            simp only [PrefixTree.rippleNonempty, PrefixSemigroup.mul] at h
            cases hrem : PrefixTree.rippleNonempty z zs' with
            | const qm => simp [hrem, ThreshElem.comp] at h
            | step qm tm =>
              simp only [hrem, ThreshElem.comp] at h
              by_cases h1 : q₀ ≥ tm
              · simp [h1] at h
              · by_cases h2 : q₀ + 1 < tm
                · simp [h1, h2] at h
                · simp only [h1, h2, ↓reduceIte, ThreshElem.step.injEq] at h
                  exact h.2.symm
        simp only [PrefixTree.rippleNonempty, PrefixSemigroup.mul, ResonantChain]
        constructor
        · rintro ⟨q, t, h⟩
          cases hrem : PrefixTree.rippleNonempty (.step q₂ t₂) ys with
          | const qm => simp [hrem, ThreshElem.comp] at h
          | step qm tm =>
            have htm : tm = t₂ := hhead q₂ t₂ ys qm tm hrem
            simp only [hrem, ThreshElem.comp] at h
            by_cases h1 : q₁ ≥ tm
            · simp [h1] at h
            · by_cases h2 : q₁ + 1 < tm
              · simp [h1, h2] at h
              · refine ⟨by omega, (ih (.step q₂ t₂)).mp ⟨qm, tm, hrem⟩⟩
        · rintro ⟨hlock, hres⟩
          rcases (ih (.step q₂ t₂)).mpr hres with ⟨qm, tm, hrem⟩
          have htm : tm = t₂ := hhead q₂ t₂ ys qm tm hrem
          refine ⟨qm, t₁, ?_⟩
          simp only [hrem, ThreshElem.comp]
          have h1 : ¬ (q₁ ≥ tm) := by omega
          have h2 : ¬ (q₁ + 1 < tm) := by omega
          simp [h1, h2]

/-- **Theorem 5a (Universal Exact Carry-Absorption Law — `∀ w ≥ 1`, ANY Prefix Tree):**
For any binary prefix tree `t` of any width `w ≥ 1` over `ThreshElem`,
`t.eval id` completely absorbs the incoming carry (`∃ q, t.eval id = .const q`)
**if and only if** its leaf sequence fails `ResonantChain`. -/
theorem tree_exact_carry_absorption (t : PrefixTree ThreshElem) :
    (∃ q, t.eval id = .const q) ↔ ¬ ResonantChain t.fringe := by
  rcases t.fringe_nonempty with ⟨x, xs, hfr⟩
  have heval : t.eval id = PrefixTree.rippleNonempty x xs := by
    have h := PrefixTree.eval_eq_rippleNonempty (M := ThreshElem) id t x xs hfr
    simpa using h
  rw [hfr, heval]
  have hiff := rippleNonempty_step_iff x xs
  cases hres : PrefixTree.rippleNonempty x xs with
  | const q =>
    constructor
    · intro _ hchain
      rcases hiff.mpr hchain with ⟨q', t', hstep⟩
      rw [hres] at hstep
      exact ThreshElem.noConfusion hstep
    · intro _; exact ⟨q, rfl⟩
  | step q t' =>
    constructor
    · rintro ⟨q', hq'⟩; exact ThreshElem.noConfusion hq'
    · intro hnot
      exact False.elim (hnot (hiff.mp ⟨q, t', hres⟩))

-- ----------------------------------------------------------------------------
-- Exact 3-Input Binary (x+y+z) & Signed 3-Input (x+y-z) Carry-Absorption Laws
-- ----------------------------------------------------------------------------

theorem enc3Bit_eq (s : Nat) (hs : s ≤ 3) :
    enc3Bit s = .step ((s / 2 : Nat) : Int) (2 - ((s % 2 : Nat) : Int)) := by
  have : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> decide

theorem encSigned3Bit_eq (s : Nat) (hs : s ≤ 3) :
    encSigned3Bit s = .step (((s / 2 : Nat) : Int) - 1) (1 - ((s % 2 : Nat) : Int)) := by
  have : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> decide

theorem resonantChain_enc3Bit_iff (ds : List Nat) (hds : ∀ s ∈ ds, s ≤ 3) :
    ResonantChain (ds.map enc3Bit) ↔ BitResonant3 ds = true := by
  induction ds with
  | nil => simp [ResonantChain, BitResonant3]
  | cons s₁ rest ih =>
    cases rest with
    | nil =>
      have hs₁ : s₁ ≤ 3 := hds s₁ (by simp)
      rw [List.map_cons, List.map_nil, enc3Bit_eq s₁ hs₁]
      simp [ResonantChain, BitResonant3]
    | cons s₂ tail =>
      have hs₁ : s₁ ≤ 3 := hds s₁ (by simp)
      have hs₂ : s₂ ≤ 3 := hds s₂ (by simp)
      have htail : ∀ s ∈ s₂ :: tail, s ≤ 3 := fun s hs => hds s (by simp [hs])
      have ih' := ih htail
      rw [List.map_cons, List.map_cons, enc3Bit_eq s₁ hs₁, enc3Bit_eq s₂ hs₂]
      rw [List.map_cons, enc3Bit_eq s₂ hs₂] at ih'
      simp only [ResonantChain, BitResonant3, Bool.and_eq_true, beq_iff_eq]
      rw [ih']
      constructor <;> (rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩)

theorem resonantChain_encSigned3Bit_iff (ds : List Nat) (hds : ∀ s ∈ ds, s ≤ 3) :
    ResonantChain (ds.map encSigned3Bit) ↔ BitResonant3 ds = true := by
  induction ds with
  | nil => simp [ResonantChain, BitResonant3]
  | cons s₁ rest ih =>
    cases rest with
    | nil =>
      have hs₁ : s₁ ≤ 3 := hds s₁ (by simp)
      rw [List.map_cons, List.map_nil, encSigned3Bit_eq s₁ hs₁]
      simp [ResonantChain, BitResonant3]
    | cons s₂ tail =>
      have hs₁ : s₁ ≤ 3 := hds s₁ (by simp)
      have hs₂ : s₂ ≤ 3 := hds s₂ (by simp)
      have htail : ∀ s ∈ s₂ :: tail, s ≤ 3 := fun s hs => hds s (by simp [hs])
      have ih' := ih htail
      rw [List.map_cons, List.map_cons, encSigned3Bit_eq s₁ hs₁, encSigned3Bit_eq s₂ hs₂]
      rw [List.map_cons, encSigned3Bit_eq s₂ hs₂] at ih'
      simp only [ResonantChain, BitResonant3, Bool.and_eq_true, beq_iff_eq]
      rw [ih']
      constructor <;> (rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩)

/-- **Theorem 5b (Exact 3-Input & Signed-3-Input Bit-Level Carry-Absorption Law — `∀ w ≥ 1`):**
For ANY prefix tree `t` of 3-input column sums `s_i ∈ {0,1,2,3}` (any width `w ≥ 1`),
BOTH unsigned 3-input addition (`x + y + z`) AND signed 3-input add-subtract (`x + y - z`)
absorb the incoming carry iff `BitResonant3 t.fringe = false`! -/
theorem three_input_exact_absorption (t : PrefixTree Nat) (hds : ∀ s ∈ t.fringe, s ≤ 3) :
    ((∃ q, t.eval enc3Bit = .const q) ↔ BitResonant3 t.fringe = false) ∧
    ((∃ q, t.eval encSigned3Bit = .const q) ↔ BitResonant3 t.fringe = false) := by
  have map_tree : ∀ (f : Nat → ThreshElem) (tr : PrefixTree Nat),
      ∃ tr' : PrefixTree ThreshElem, tr'.fringe = tr.fringe.map f ∧ tr'.eval id = tr.eval f := by
    intro f tr
    induction tr with
    | leaf a => exact ⟨.leaf (f a), rfl, rfl⟩
    | node lo hi ihlo ihhi =>
      rcases ihlo with ⟨lo', hflo, helo⟩
      rcases ihhi with ⟨hi', hfhi, hehi⟩
      refine ⟨.node lo' hi', ?_, ?_⟩
      · simp [PrefixTree.fringe, hflo, hfhi]
      · simp [PrefixTree.eval, helo, hehi]
  rcases map_tree enc3Bit t with ⟨t₁, hf₁, he₁⟩
  rcases map_tree encSigned3Bit t with ⟨t₂, hf₂, he₂⟩
  have h1 := tree_exact_carry_absorption t₁
  have h2 := tree_exact_carry_absorption t₂
  rw [hf₁, he₁, resonantChain_enc3Bit_iff t.fringe hds] at h1
  rw [hf₂, he₂, resonantChain_encSigned3Bit_iff t.fringe hds] at h2
  constructor
  · rw [h1]; cases BitResonant3 t.fringe <;> simp
  · rw [h2]; cases BitResonant3 t.fringe <;> simp

-- ----------------------------------------------------------------------------
-- Exact Infinite Counting Laws (∀ w ≥ 1): 2^(w+1) Digit Strings & 2*4^w Triples
-- ----------------------------------------------------------------------------

theorem sumWeights3_append (l₁ l₂ : List (List Nat)) :
    sumWeights3 (l₁ ++ l₂) = sumWeights3 l₁ + sumWeights3 l₂ := by
  induction l₁ with
  | nil => simp [sumWeights3]
  | cons x xs ih => simp [sumWeights3, ih, Nat.add_assoc]

theorem sumWeights3_map_cons (s : Nat) (l : List (List Nat)) :
    sumWeights3 (l.map (fun ds => s :: ds)) = digitWeight3 s * sumWeights3 l := by
  induction l with
  | nil => simp [sumWeights3]
  | cons x xs ih =>
    simp only [List.map_cons, sumWeights3, stringWeight3, ih]
    rw [Nat.mul_add]

theorem allDigits3_length (w : Nat) : (allDigits3 w).length = 4 ^ w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp only [allDigits3, List.length_append, List.length_map, ih, Nat.pow_succ]
    omega

theorem allDigits3_total_triples (w : Nat) : sumWeights3 (allDigits3 w) = 8 ^ w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp only [allDigits3]
    rw [sumWeights3_append, sumWeights3_append, sumWeights3_append]
    rw [sumWeights3_map_cons, sumWeights3_map_cons, sumWeights3_map_cons, sumWeights3_map_cons]
    rw [ih]
    simp only [digitWeight3, Nat.pow_succ]
    omega

theorem allDigits3_succ_nonempty (w : Nat) : ∀ ds ∈ allDigits3 (w + 1), ds ≠ [] := by
  intro ds hds
  simp only [allDigits3, List.mem_append, List.mem_map] at hds
  rcases hds with (((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) <;> simp

theorem filter_map_cons (s : Nat) (p : List Nat → Bool) (l : List (List Nat)) :
    (l.map (fun ds => s :: ds)).filter p =
      (l.filter (fun ds => p (s :: ds))).map (fun ds => s :: ds) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.filter_cons]
    cases p (s :: x) <;> simp [ih]

theorem filter_ext (l : List (List Nat)) (p q : List Nat → Bool)
    (hpq : ∀ x ∈ l, p x = q x) : l.filter p = l.filter q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons, hpq x (by simp)]
    rw [ih (fun y hy => hpq y (by simp [hy]))]

theorem filter_false_nil (l : List (List Nat)) :
    l.filter (fun _ => false) = [] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem bitResonant3_cons_of_ne (s : Nat) (ds : List Nat) (hne : ds ≠ []) :
    BitResonant3 (s :: ds) = ((s / 2 + ds.headD 0 % 2 == 1) && BitResonant3 ds) := by
  cases ds with
  | nil => exact False.elim (hne rfl)
  | cons _ _ => rfl

theorem res_parity_eq (s : Nat) (hs : s ≤ 3) (d : Nat) :
    (s / 2 + d % 2 == 1) = (d % 2 == 1 - s / 2) := by
  have hd : d % 2 = 0 ∨ d % 2 = 1 := by omega
  have hs' : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by omega
  rcases hs' with rfl | rfl | rfl | rfl <;> rcases hd with h | h <;> simp [h]

/-- Helper splitting resonant strings by their first digit's parity (`even` vs `odd`). -/
theorem resonant_counts_split (w : Nat) :
    ((allDigits3 (w + 1)).filter (fun ds => BitResonant3 ds && (ds.headD 0 % 2 == 0))).length = 2 ^ (w + 1) ∧
    ((allDigits3 (w + 1)).filter (fun ds => BitResonant3 ds && (ds.headD 0 % 2 == 1))).length = 2 ^ (w + 1) := by
  induction w with
  | zero => decide
  | succ w ih =>
    rcases ih with ⟨ihe, iho⟩
    have hlen_case : ∀ (s b : Nat), s ≤ 3 →
        (((allDigits3 (w + 1)).map (fun ds => s :: ds)).filter
          (fun ds => BitResonant3 ds && (ds.headD 0 % 2 == b))).length =
        if s % 2 == b then
          ((allDigits3 (w + 1)).filter
            (fun ds => BitResonant3 ds && (ds.headD 0 % 2 == (1 - s / 2)))).length
        else 0 := by
      intro s b hs
      rw [filter_map_cons, List.length_map]
      by_cases hsb : (s % 2 == b) = true
      · simp only [hsb, ↓reduceIte]
        congr 1
        apply filter_ext
        intro ds hds
        rw [bitResonant3_cons_of_ne s ds (allDigits3_succ_nonempty w ds hds)]
        simp only [List.headD_cons, hsb, Bool.and_true]
        rw [res_parity_eq s hs (ds.headD 0), Bool.and_comm]
      · simp only [Bool.not_eq_true] at hsb
        simp only [hsb, Bool.false_eq_true, ↓reduceIte]
        have h0 : ∀ ds ∈ allDigits3 (w + 1),
            (BitResonant3 (s :: ds) && ((s :: ds).headD 0 % 2 == b)) = false := by
          intro ds _; simp [hsb]
        rw [filter_ext _ _ (fun _ => false) h0, filter_false_nil]
        rfl
    constructor
    · rw [allDigits3]
      simp only [List.filter_append, List.length_append]
      rw [hlen_case 0 0 (by omega), hlen_case 1 0 (by omega),
          hlen_case 2 0 (by omega), hlen_case 3 0 (by omega)]
      simp only [List.headD_eq_head?_getD] at ihe iho
      simp [ihe, iho, Nat.pow_succ]
      omega
    · rw [allDigits3]
      simp only [List.filter_append, List.length_append]
      rw [hlen_case 0 1 (by omega), hlen_case 1 1 (by omega),
          hlen_case 2 1 (by omega), hlen_case 3 1 (by omega)]
      simp only [List.headD_eq_head?_getD] at ihe iho
      simp [ihe, iho, Nat.pow_succ]
      omega

/-- **Theorem 5c (Exact Infinite 3-Input Digit-String Propagation Count — `∀ w ≥ 1`):**
Out of all `4^w` width-`w` 3-input column-sum strings, **exactly `2^(w + 1)`** propagate
carry (and `4^w - 2^(w + 1)` completely absorb it). -/
theorem three_input_resonant_digit_count (w : Nat) (hw : 1 ≤ w) :
    ((allDigits3 w).filter BitResonant3).length = 2 ^ (w + 1) := by
  cases w with
  | zero => omega
  | succ k =>
    rcases resonant_counts_split k with ⟨he, ho⟩
    have hpart : ∀ (l : List (List Nat)),
        (l.filter BitResonant3).length =
          (l.filter (fun ds => BitResonant3 ds && (ds.headD 0 % 2 == 0))).length +
          (l.filter (fun ds => BitResonant3 ds && (ds.headD 0 % 2 == 1))).length := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.filter_cons]
        cases hbr : BitResonant3 x with
        | false => simp [ih]
        | true =>
          have hmod : x.headD 0 % 2 = 0 ∨ x.headD 0 % 2 = 1 := by omega
          rcases hmod with h0 | h1
          · simp only [Bool.true_and, h0, beq_self_eq_true, ↓reduceIte, List.length_cons]
            have h01 : (0 == 1) = false := rfl
            simp only [h01, Bool.false_eq_true, ↓reduceIte]
            omega
          · simp only [Bool.true_and, h1, beq_self_eq_true, ↓reduceIte, List.length_cons]
            have h10 : (1 == 0) = false := rfl
            simp only [h10, Bool.false_eq_true, ↓reduceIte]
            omega
    rw [hpart, he, ho, Nat.pow_succ]
    omega

/-- Weighted Markov eigenvector split for binary triples `(x, y, z) ∈ ({0,1}^w)^3`. -/
theorem resonant_triples_split (w : Nat) :
    sumWeights3 ((allDigits3 (w + 1)).filter (fun ds => BitResonant3 ds && (ds.headD 0 % 2 == 0))) = 4 ^ (w + 1) ∧
    sumWeights3 ((allDigits3 (w + 1)).filter (fun ds => BitResonant3 ds && (ds.headD 0 % 2 == 1))) = 4 ^ (w + 1) := by
  induction w with
  | zero => decide
  | succ w ih =>
    rcases ih with ⟨ihe, iho⟩
    have hwt_case : ∀ (s b : Nat), s ≤ 3 →
        sumWeights3 (((allDigits3 (w + 1)).map (fun ds => s :: ds)).filter
          (fun ds => BitResonant3 ds && (ds.headD 0 % 2 == b))) =
        if s % 2 == b then
          digitWeight3 s * sumWeights3 ((allDigits3 (w + 1)).filter
            (fun ds => BitResonant3 ds && (ds.headD 0 % 2 == (1 - s / 2))))
        else 0 := by
      intro s b hs
      rw [filter_map_cons, sumWeights3_map_cons]
      by_cases hsb : (s % 2 == b) = true
      · simp only [hsb, ↓reduceIte]
        congr 2
        apply filter_ext
        intro ds hds
        rw [bitResonant3_cons_of_ne s ds (allDigits3_succ_nonempty w ds hds)]
        simp only [List.headD_cons, hsb, Bool.and_true]
        rw [res_parity_eq s hs (ds.headD 0), Bool.and_comm]
      · simp only [Bool.not_eq_true] at hsb
        simp only [hsb, Bool.false_eq_true, ↓reduceIte]
        have h0 : ∀ ds ∈ allDigits3 (w + 1),
            (BitResonant3 (s :: ds) && ((s :: ds).headD 0 % 2 == b)) = false := by
          intro ds _; simp [hsb]
        rw [filter_ext _ _ (fun _ => false) h0, filter_false_nil]
        simp [sumWeights3]
    constructor
    · rw [allDigits3]
      simp only [List.filter_append]
      rw [sumWeights3_append, sumWeights3_append, sumWeights3_append]
      rw [hwt_case 0 0 (by omega), hwt_case 1 0 (by omega),
          hwt_case 2 0 (by omega), hwt_case 3 0 (by omega)]
      simp only [List.headD_eq_head?_getD] at ihe iho
      simp [digitWeight3, ihe, iho, Nat.pow_succ]
      omega
    · rw [allDigits3]
      simp only [List.filter_append]
      rw [sumWeights3_append, sumWeights3_append, sumWeights3_append]
      rw [hwt_case 0 1 (by omega), hwt_case 1 1 (by omega),
          hwt_case 2 1 (by omega), hwt_case 3 1 (by omega)]
      simp only [List.headD_eq_head?_getD] at ihe iho
      simp [digitWeight3, ihe, iho, Nat.pow_succ]
      omega

/-- **Theorem 5d (Exact Infinite 3-Input Binary-Triple Propagation Count — `∀ w ≥ 1`):**
Out of all `8^w` binary input triples `(x, y, z) ∈ ({0, 1}^w)^3`, **exactly `2 * 4^w`**
propagate carry across width `w` (exact absorption fraction `1 - 2^{-(w-1)}`). -/
theorem three_input_resonant_triple_count (w : Nat) (hw : 1 ≤ w) :
    sumWeights3 ((allDigits3 w).filter BitResonant3) = 2 * 4 ^ w := by
  cases w with
  | zero => omega
  | succ k =>
    rcases resonant_triples_split k with ⟨he, ho⟩
    have hpart : ∀ (l : List (List Nat)),
        sumWeights3 (l.filter BitResonant3) =
          sumWeights3 (l.filter (fun ds => BitResonant3 ds && (ds.headD 0 % 2 == 0))) +
          sumWeights3 (l.filter (fun ds => BitResonant3 ds && (ds.headD 0 % 2 == 1))) := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih =>
        have hsplit : ∀ (p : List Nat → Bool),
            sumWeights3 ((x :: xs).filter p) =
              (if p x then stringWeight3 x else 0) + sumWeights3 (xs.filter p) := by
          intro p
          simp only [List.filter_cons]
          cases p x <;> simp [sumWeights3]
        rw [hsplit, hsplit, hsplit, ih]
        cases hbr : BitResonant3 x with
        | false => simp
        | true =>
          have hmod : x.headD 0 % 2 = 0 ∨ x.headD 0 % 2 = 1 := by omega
          rcases hmod with h0 | h1
          · simp only [Bool.true_and, h0, beq_self_eq_true, ↓reduceIte]
            have h01 : (0 == 1) = false := rfl
            simp only [h01, Bool.false_eq_true, ↓reduceIte]
            omega
          · simp only [Bool.true_and, h1, beq_self_eq_true, ↓reduceIte]
            have h10 : (1 == 0) = false := rfl
            simp only [h10, Bool.false_eq_true, ↓reduceIte]
            omega
    rw [hpart, he, ho]
    omega

-- ============================================================================
-- 6. Modulo-(M - δ) Crandall/Mersenne & Modulo-(M + 1) Fermat Feedback Theorems
-- ============================================================================

/-- **Theorem 6a (Exact Modulo-`(M - δ)` Crandall / Mersenne Feedback Dichotomy):**
For any `δ ≥ 1`, modulus `M > δ` with `M ≥ δ * (U - L)`, and any sum `S` whose feedback map
`G_δ(c) = ⌊(δc + S) / M⌋` preserves `[L, U]`:
1. `e = collapse (δL) (δU) (M, S)` represents `G_δ` via `G_δ(c) = e.eval (δc)`.
2. Dual fixed points `{q, q + 1}` occur iff `isCrandallDual δ e`, iff `(q+1)(M-δ) ≤ S < (q+1)(M-δ) + δ`.
3. Outside the dual band, `c* = crandallFixedPoint δ e` is the UNIQUE fixed point and
   `G_δ(G_δ(c₀)) = c*` for ALL `c₀ ∈ [L, U]` (2-step global stabilization).
4. For ANY fixed point `c*`, the residue `R = (δc* + S) mod M` satisfies `0 ≤ R < M` and
   `(M - δ) ∣ (R - S)`; in the dual band, the canonical upper fixed point `q + 1` gives `0 ≤ R < δ`
   (canonical `< M - δ` whenever `M ≥ 2δ`). -/
theorem crandall_feedback_dichotomy (L U δ S : Int) (M : Nat)
    (hLU : L ≤ U) (hδ : 1 ≤ δ) (hMgt : δ < (M : Int))
    (hMspan : δ * (U - L) ≤ (M : Int))
    (hpres : ∀ c : Int, L ≤ c → c ≤ U →
      L ≤ (δ * c + S) / (M : Int) ∧ (δ * c + S) / (M : Int) ≤ U) :
    let m : Int := (M : Int) - δ
    let G : Int → Int := fun c => (δ * c + S) / (M : Int)
    let d : DivElem := ⟨M, by omega, S⟩
    let e : ThreshElem := collapse (δ * L) (δ * U) d
    -- (1) Exact representation
    (∀ c, L ≤ c → c ≤ U → G c = e.eval (δ * c)) ∧
    -- (2) Dual-band exact arithmetic characterization
    (∀ q t, e = .step q t →
      (isCrandallDual δ e ↔ (q + 1) * m ≤ S ∧ S < (q + 1) * m + δ)) ∧
    -- (3) Dual-band gives both q and q+1 as fixed points with 0 ≤ R(q+1) < δ
    (∀ q t, e = .step q t → isCrandallDual δ e →
      G q = q ∧ G (q + 1) = q + 1 ∧
      0 ≤ (δ * (q + 1) + S) % (M : Int) ∧
      (δ * (q + 1) + S) % (M : Int) < δ ∧
      ∃ k : Int, (δ * (q + 1) + S) % (M : Int) - S = m * k) ∧
    -- (4) Outside dual band: unique fixed point + 2-step stabilization
    (¬ isCrandallDual δ e →
      let cStar := crandallFixedPoint δ e
      L ≤ cStar ∧ cStar ≤ U ∧ G cStar = cStar ∧
      (∀ c, L ≤ c → c ≤ U → G c = c → c = cStar) ∧
      (∀ c₀, L ≤ c₀ → c₀ ≤ U → G (G c₀) = cStar)) ∧
    -- (5) Exact modular congruence for EVERY fixed point
    (∀ cStar, G cStar = cStar →
      0 ≤ (δ * cStar + S) % (M : Int) ∧
      (δ * cStar + S) % (M : Int) < (M : Int) ∧
      ∃ k : Int, (δ * cStar + S) % (M : Int) - S = m * k) := by
  intro m G d e
  have hMpos : (0 : Int) < (M : Int) := by omega
  have hspan' : δ * U - δ * L ≤ (d.mod : Int) := by
    simp only [d]; rw [← Int.mul_sub]; exact hMspan
  have hrep : ∀ c, L ≤ c → c ≤ U → G c = e.eval (δ * c) := by
    intro c hcL hcU
    have h1 : δ * L ≤ δ * c := Int.mul_le_mul_of_nonneg_left hcL (by omega)
    have h2 : δ * c ≤ δ * U := Int.mul_le_mul_of_nonneg_left hcU (by omega)
    exact (collapse_sound (δ * L) (δ * U) d hspan' (δ * c) h1 h2).symm
  have hq_bounds : ∀ q, e = .const q → L ≤ q ∧ q ≤ U := by
    intro q hq
    have hG := hrep L (Int.le_refl L) hLU
    rw [hq] at hG
    simp only [ThreshElem.eval, G] at hG
    have hp := hpres L (Int.le_refl L) hLU
    omega
  have hstep_qr : ∀ q t, e = .step q t →
      q = (δ * L + S) / (M : Int) ∧
      t = δ * L + (M : Int) - (δ * L + S) % (M : Int) ∧
      ¬ ((δ * L + S) % (M : Int) + (δ * U - δ * L) < (M : Int)) := by
    intro q t hst
    unfold e collapse at hst
    simp only [d] at hst
    by_cases habs : (δ * L + S) % (M : Int) + (δ * U - δ * L) < (M : Int)
    · simp only [habs, ↓reduceIte] at hst
      exact ThreshElem.noConfusion hst
    · simp only [habs, ↓reduceIte, ThreshElem.step.injEq] at hst
      exact ⟨hst.1.symm, hst.2.symm, habs⟩
  have hstep_bounds : ∀ q t, e = .step q t →
      L ≤ q ∧ q + 1 ≤ U ∧ δ * L < t ∧ t ≤ δ * U := by
    intro q t hst
    rcases hstep_qr q t hst with ⟨_, ht_eq, hnabs⟩
    have hGL := hrep L (Int.le_refl L) hLU
    have hGU := hrep U hLU (Int.le_refl U)
    have hpL := hpres L (Int.le_refl L) hLU
    have hpU := hpres U hLU (Int.le_refl U)
    have hr0 : 0 ≤ (δ * L + S) % (M : Int) := Int.emod_nonneg _ (by omega)
    have hrm : (δ * L + S) % (M : Int) < (M : Int) := Int.emod_lt_of_pos _ hMpos
    have ht : δ * L < t ∧ t ≤ δ * U := by omega
    rw [hst] at hGL hGU
    simp only [ThreshElem.eval, G] at hGL hGU
    have h1 : ¬ (δ * L ≥ t) := by omega
    have h2 : δ * U ≥ t := by omega
    simp only [h1, ↓reduceIte] at hGL
    simp only [h2, ↓reduceIte] at hGU
    exact ⟨by omega, by omega, ht.1, ht.2⟩
  have hmod_fp : ∀ cStar, G cStar = cStar →
      0 ≤ (δ * cStar + S) % (M : Int) ∧
      (δ * cStar + S) % (M : Int) < (M : Int) ∧
      ∃ k : Int, (δ * cStar + S) % (M : Int) - S = m * k := by
    intro cStar hfp
    have hdiv := Int.mul_ediv_add_emod (δ * cStar + S) (M : Int)
    have hrem0 : 0 ≤ (δ * cStar + S) % (M : Int) := Int.emod_nonneg _ (by omega)
    have hremm : (δ * cStar + S) % (M : Int) < (M : Int) := Int.emod_lt_of_pos _ hMpos
    refine ⟨hrem0, hremm, ⟨-cStar, ?_⟩⟩
    have hfp' : (δ * cStar + S) / (M : Int) = cStar := hfp
    rw [hfp'] at hdiv
    have hmk : m * (-cStar) = -((M : Int) * cStar) + δ * cStar := by
      simp only [m]
      rw [Int.mul_neg, Int.sub_mul]
      omega
    omega
  refine ⟨hrep, ?_, ?_, ?_, hmod_fp⟩
  · -- (2) Dual-band arithmetic characterization
    intro q t hst
    rcases hstep_qr q t hst with ⟨hq_eq, ht_eq, _⟩
    have hdiv := Int.mul_ediv_add_emod (δ * L + S) (M : Int)
    rw [← hq_eq] at hdiv
    simp only [hst, isCrandallDual]
    have hqm : (q + 1) * m = (M : Int) * q + (M : Int) - δ * (q + 1) := by
      simp only [m]
      rw [Int.mul_sub, Int.add_mul, Int.one_mul, Int.mul_comm q (M : Int), Int.mul_comm (q + 1) δ]
    have hδq : δ * (q + 1) = δ * q + δ := by rw [Int.mul_add, Int.mul_one]
    constructor <;> intro ⟨h1, h2⟩ <;> omega
  · -- (3) Dual-band fixed points & tight remainder bound 0 ≤ R(q+1) < δ
    intro q t hst hdual
    rcases hstep_bounds q t hst with ⟨hqL, hqU, _, _⟩
    rcases hstep_qr q t hst with ⟨hq_eq, ht_eq, _⟩
    simp only [hst, isCrandallDual] at hdual
    have hGq : G q = q := by
      rw [hrep q hqL (by omega), hst]
      simp only [ThreshElem.eval]
      have : ¬ (δ * q ≥ t) := by omega
      simp [this]
    have hGq1 : G (q + 1) = q + 1 := by
      rw [hrep (q + 1) (by omega) hqU, hst]
      simp only [ThreshElem.eval]
      have : δ * (q + 1) ≥ t := by omega
      simp [this]
    have hdivL := Int.mul_ediv_add_emod (δ * L + S) (M : Int)
    rw [← hq_eq] at hdivL
    have hdivq1 := Int.mul_ediv_add_emod (δ * (q + 1) + S) (M : Int)
    have hGq1' : (δ * (q + 1) + S) / (M : Int) = q + 1 := hGq1
    rw [hGq1'] at hdivq1
    have hrem0 : 0 ≤ (δ * (q + 1) + S) % (M : Int) := Int.emod_nonneg _ (by omega)
    have hmulq1 : (M : Int) * (q + 1) = (M : Int) * q + (M : Int) := by
      rw [Int.mul_add, Int.mul_one]
    have hδq : δ * (q + 1) = δ * q + δ := by rw [Int.mul_add, Int.mul_one]
    have hrem_lt_δ : (δ * (q + 1) + S) % (M : Int) < δ := by omega
    exact ⟨hGq, hGq1, hrem0, hrem_lt_δ, (hmod_fp (q + 1) hGq1).2.2⟩
  · -- (4) Outside dual band: unique fixed point & 2-step stabilization
    intro hnotdual
    cases he : e with
    | const q =>
      rcases hq_bounds q he with ⟨hqL, hqU⟩
      have hGconst : ∀ c, L ≤ c → c ≤ U → G c = q := by
        intro c hcL hcU
        rw [hrep c hcL hcU, he]; rfl
      simp only [crandallFixedPoint]
      refine ⟨hqL, hqU, hGconst q hqL hqU, ?_, ?_⟩
      · intro c hcL hcU hfp
        rw [hGconst c hcL hcU] at hfp
        exact hfp.symm
      · intro c₀ hc₀L hc₀U
        rw [hGconst c₀ hc₀L hc₀U, hGconst q hqL hqU]
    | step q t =>
      rcases hstep_bounds q t he with ⟨hqL, hqU, _, _⟩
      simp only [he, isCrandallDual] at hnotdual
      have hGstep : ∀ c, L ≤ c → c ≤ U → G c = if δ * c ≥ t then q + 1 else q := by
        intro c hcL hcU
        rw [hrep c hcL hcU, he]; rfl
      have hδq : δ * (q + 1) = δ * q + δ := by rw [Int.mul_add, Int.mul_one]
      by_cases hcase : δ * (q + 1) ≥ t
      · have hδq_ge : δ * q ≥ t := by omega
        have hcStar : crandallFixedPoint δ (.step q t) = q + 1 := by
          simp [crandallFixedPoint, hcase]
        simp only [hcStar]
        refine ⟨by omega, hqU, ?_, ?_, ?_⟩
        · rw [hGstep (q + 1) (by omega) hqU]; simp [hcase]
        · intro c hcL hcU hfp
          rw [hGstep c hcL hcU] at hfp
          by_cases hc : δ * c ≥ t
          · simp only [hc, ↓reduceIte] at hfp; exact hfp.symm
          · simp only [hc, ↓reduceIte] at hfp; subst hfp; omega
        · intro c₀ hc₀L hc₀U
          rw [hGstep c₀ hc₀L hc₀U]
          by_cases hc : δ * c₀ ≥ t
          · simp only [hc, ↓reduceIte]; rw [hGstep (q + 1) (by omega) hqU]; simp [hcase]
          · simp only [hc, ↓reduceIte]; rw [hGstep q hqL (by omega)]; simp [hδq_ge]
      · have hδq_lt : ¬ (δ * q ≥ t) := by omega
        have hcStar : crandallFixedPoint δ (.step q t) = q := by
          simp [crandallFixedPoint, hcase]
        simp only [hcStar]
        refine ⟨hqL, by omega, ?_, ?_, ?_⟩
        · rw [hGstep q hqL (by omega)]; simp [hδq_lt]
        · intro c hcL hcU hfp
          rw [hGstep c hcL hcU] at hfp
          by_cases hc : δ * c ≥ t
          · simp only [hc, ↓reduceIte] at hfp; subst hfp; omega
          · simp only [hc, ↓reduceIte] at hfp; exact hfp.symm
        · intro c₀ hc₀L hc₀U
          rw [hGstep c₀ hc₀L hc₀U]
          by_cases hc : δ * c₀ ≥ t
          · simp only [hc, ↓reduceIte]; rw [hGstep (q + 1) (by omega) hqU]; simp [hcase]
          · simp only [hc, ↓reduceIte]; rw [hGstep q hqL (by omega)]; simp [hδq_lt]

/-- Sharpness witness for `M < 2δ` in Crandall feedback (`M = 7, δ = 5, m = 2, S = 4`):
the upper fixed point `c* = 1` gives `R = 2 ≥ m = 2` (though `R < δ = 5`). -/
theorem crandall_noncanonical_witness :
    let M : Int := 7; let δ : Int := 5; let S : Int := 4
    (δ * 1 + S) / M = 1 ∧ (δ * 1 + S) % M = 2 ∧ 2 ≥ M - δ := by
  decide

/-- **Theorem 6b (Exact Modulo-`(M + 1)` Fermat Negative-Feedback Dichotomy):**
For any `M ≥ U - L` (`M ≥ 1`) and any `S` whose negative feedback map
`H(c) = ⌊(-c + S) / M⌋` preserves `[L, U]`:
1. `H` has NO fixed point in `[L, U]` iff `e = step q (-q)` iff `S = (q + 1)(M + 1) - 1`,
   in which case `q ↔ q + 1` is an exact period-2 limit cycle.
2. Otherwise, `c* = fermatFixedPoint e` is the UNIQUE fixed point, reached in `≤ 2` steps
   (`H(H(c₀)) = c*`), and `R = (-c* + S) mod M` satisfies `0 ≤ R < M` and `(M + 1) ∣ (R - S)`. -/
theorem fermat_feedback_dichotomy (L U S : Int) (M : Nat)
    (hLU : L ≤ U) (hMpos : 0 < M) (hMspan : U - L ≤ (M : Int))
    (hpres : ∀ c : Int, L ≤ c → c ≤ U →
      L ≤ (-c + S) / (M : Int) ∧ (-c + S) / (M : Int) ≤ U) :
    let m : Int := (M : Int) + 1
    let H : Int → Int := fun c => (-c + S) / (M : Int)
    let d : DivElem := ⟨M, hMpos, S⟩
    let e : ThreshElem := collapse (-U) (-L) d
    -- (1) Exact representation
    (∀ c, L ≤ c → c ≤ U → H c = e.eval (-c)) ∧
    -- (2) Period-2 oscillation exact characterization
    (∀ q t, e = .step q t → (q + t = 0 ↔ S = (q + 1) * m - 1)) ∧
    (∀ q, e = .step q (-q) →
      L ≤ q ∧ q + 1 ≤ U ∧ H q = q + 1 ∧ H (q + 1) = q ∧
      ∀ c, L ≤ c → c ≤ U → H c ≠ c) ∧
    -- (3) Outside oscillation: unique fixed point + 2-step stabilization + exact mod (M+1)
    ((¬ ∃ q, e = .step q (-q)) →
      let cStar := fermatFixedPoint e
      L ≤ cStar ∧ cStar ≤ U ∧ H cStar = cStar ∧
      (∀ c, L ≤ c → c ≤ U → H c = c → c = cStar) ∧
      (∀ c₀, L ≤ c₀ → c₀ ≤ U → H (H c₀) = cStar) ∧
      0 ≤ (-cStar + S) % (M : Int) ∧
      (-cStar + S) % (M : Int) < (M : Int) ∧
      ∃ k : Int, (-cStar + S) % (M : Int) - S = m * k) := by
  intro m H d e
  have hMpos' : (0 : Int) < (M : Int) := by omega
  have hspan' : (-L) - (-U) ≤ (d.mod : Int) := by simp only [d]; omega
  have hrep : ∀ c, L ≤ c → c ≤ U → H c = e.eval (-c) := by
    intro c hcL hcU
    exact (collapse_sound (-U) (-L) d hspan' (-c) (by omega) (by omega)).symm
  have hq_bounds : ∀ q, e = .const q → L ≤ q ∧ q ≤ U := by
    intro q hq
    have hH := hrep L (Int.le_refl L) hLU
    rw [hq] at hH
    simp only [ThreshElem.eval, H] at hH
    have hp := hpres L (Int.le_refl L) hLU
    omega
  have hstep_qr : ∀ q t, e = .step q t →
      q = (-U + S) / (M : Int) ∧
      t = -U + (M : Int) - (-U + S) % (M : Int) ∧
      ¬ ((-U + S) % (M : Int) + ((-L) - (-U)) < (M : Int)) := by
    intro q t hst
    unfold e collapse at hst
    simp only [d] at hst
    by_cases habs : (-U + S) % (M : Int) + ((-L) - (-U)) < (M : Int)
    · simp only [habs, ↓reduceIte] at hst
      exact ThreshElem.noConfusion hst
    · simp only [habs, ↓reduceIte, ThreshElem.step.injEq] at hst
      exact ⟨hst.1.symm, hst.2.symm, habs⟩
  have hstep_bounds : ∀ q t, e = .step q t →
      L ≤ q ∧ q + 1 ≤ U ∧ -U < t ∧ t ≤ -L := by
    intro q t hst
    rcases hstep_qr q t hst with ⟨_, ht_eq, hnabs⟩
    have hHL := hrep L (Int.le_refl L) hLU
    have hHU := hrep U hLU (Int.le_refl U)
    have hpL := hpres L (Int.le_refl L) hLU
    have hpU := hpres U hLU (Int.le_refl U)
    have hr0 : 0 ≤ (-U + S) % (M : Int) := Int.emod_nonneg _ (by omega)
    have hrm : (-U + S) % (M : Int) < (M : Int) := Int.emod_lt_of_pos _ hMpos'
    have ht : -U < t ∧ t ≤ -L := by omega
    rw [hst] at hHL hHU
    simp only [ThreshElem.eval, H] at hHL hHU
    have h1 : -L ≥ t := by omega
    have h2 : ¬ (-U ≥ t) := by omega
    simp only [h1, ↓reduceIte] at hHL
    simp only [h2, ↓reduceIte] at hHU
    exact ⟨by omega, by omega, ht.1, ht.2⟩
  have hmod_fp : ∀ cStar, H cStar = cStar →
      0 ≤ (-cStar + S) % (M : Int) ∧
      (-cStar + S) % (M : Int) < (M : Int) ∧
      ∃ k : Int, (-cStar + S) % (M : Int) - S = m * k := by
    intro cStar hfp
    have hdiv := Int.mul_ediv_add_emod (-cStar + S) (M : Int)
    have hrem0 : 0 ≤ (-cStar + S) % (M : Int) := Int.emod_nonneg _ (by omega)
    have hremm : (-cStar + S) % (M : Int) < (M : Int) := Int.emod_lt_of_pos _ hMpos'
    refine ⟨hrem0, hremm, ⟨-cStar, ?_⟩⟩
    have hfp' : (-cStar + S) / (M : Int) = cStar := hfp
    rw [hfp'] at hdiv
    have hmk : m * (-cStar) = -((M : Int) * cStar) - cStar := by
      simp only [m]
      rw [Int.mul_neg, Int.add_mul, Int.one_mul]
      omega
    omega
  refine ⟨hrep, ?_, ?_, ?_⟩
  · -- (2a) Arithmetic characterization q + t = 0 ↔ S = (q+1)(M+1) - 1
    intro q t hst
    rcases hstep_qr q t hst with ⟨hq_eq, ht_eq, _⟩
    have hdiv := Int.mul_ediv_add_emod (-U + S) (M : Int)
    rw [← hq_eq] at hdiv
    have hqm : (q + 1) * m = (M : Int) * q + (M : Int) + q + 1 := by
      simp only [m]
      rw [Int.mul_add, Int.add_mul, Int.one_mul, Int.mul_one, Int.mul_comm q (M : Int)]
      omega
    omega
  · -- (2b) Period-2 oscillation and zero fixed points
    intro q hst
    rcases hstep_bounds q (-q) hst with ⟨hqL, hqU, _, _⟩
    have hHq : H q = q + 1 := by
      rw [hrep q hqL (by omega), hst]; simp [ThreshElem.eval]
    have hHq1 : H (q + 1) = q := by
      rw [hrep (q + 1) (by omega) hqU, hst]
      simp only [ThreshElem.eval]
      have : ¬ (-(q + 1) ≥ -q) := by omega
      simp [this]
    refine ⟨hqL, hqU, hHq, hHq1, ?_⟩
    intro c hcL hcU hfp
    rw [hrep c hcL hcU, hst] at hfp
    simp only [ThreshElem.eval] at hfp
    by_cases hc : -c ≥ -q
    · simp only [hc, ↓reduceIte] at hfp; omega
    · simp only [hc, ↓reduceIte] at hfp; omega
  · -- (3) Unique fixed point + 2-step stabilization
    intro hnotosc
    cases he : e with
    | const q =>
      rcases hq_bounds q he with ⟨hqL, hqU⟩
      have hHconst : ∀ c, L ≤ c → c ≤ U → H c = q := by
        intro c hcL hcU; rw [hrep c hcL hcU, he]; rfl
      have hfpq := hHconst q hqL hqU
      rcases hmod_fp q hfpq with ⟨hr0, hrm, hdiv⟩
      simp only [fermatFixedPoint]
      refine ⟨hqL, hqU, hfpq, ?_, ?_, hr0, hrm, hdiv⟩
      · intro c hcL hcU hfp; rw [hHconst c hcL hcU] at hfp; exact hfp.symm
      · intro c₀ hc₀L hc₀U; rw [hHconst c₀ hc₀L hc₀U, hHconst q hqL hqU]
    | step q t =>
      rcases hstep_bounds q t he with ⟨hqL, hqU, _, _⟩
      have hne : q + t ≠ 0 := by
        intro h0
        have ht : t = -q := by omega
        subst ht
        exact hnotosc ⟨q, he⟩
      have hHstep : ∀ c, L ≤ c → c ≤ U → H c = if -c ≥ t then q + 1 else q := by
        intro c hcL hcU; rw [hrep c hcL hcU, he]; rfl
      by_cases hgt : q + t > 0
      · have hcStar : fermatFixedPoint (.step q t) = q := by simp [fermatFixedPoint, hgt]
        simp only [hcStar]
        have hfpq : H q = q := by
          rw [hHstep q hqL (by omega)]
          have : ¬ (-q ≥ t) := by omega
          simp [this]
        have hHq1 : H (q + 1) = q := by
          rw [hHstep (q + 1) (by omega) hqU]
          have : ¬ (-(q + 1) ≥ t) := by omega
          simp [this]
        rcases hmod_fp q hfpq with ⟨hr0, hrm, hdiv⟩
        refine ⟨hqL, by omega, hfpq, ?_, ?_, hr0, hrm, hdiv⟩
        · intro c hcL hcU hfp
          rw [hHstep c hcL hcU] at hfp
          by_cases hc : -c ≥ t
          · simp only [hc, ↓reduceIte] at hfp; omega
          · simp only [hc, ↓reduceIte] at hfp; omega
        · intro c₀ hc₀L hc₀U
          rw [hHstep c₀ hc₀L hc₀U]
          by_cases hc : -c₀ ≥ t
          · simp only [hc, ↓reduceIte]; exact hHq1
          · simp only [hc, ↓reduceIte]; exact hfpq
      · have hlt : q + t < 0 := by omega
        have hcStar : fermatFixedPoint (.step q t) = q + 1 := by simp [fermatFixedPoint, hgt]
        simp only [hcStar]
        have hHq : H q = q + 1 := by
          rw [hHstep q hqL (by omega)]
          have : -q ≥ t := by omega
          simp [this]
        have hfpq1 : H (q + 1) = q + 1 := by
          rw [hHstep (q + 1) (by omega) hqU]
          have : -(q + 1) ≥ t := by omega
          simp [this]
        rcases hmod_fp (q + 1) hfpq1 with ⟨hr0, hrm, hdiv⟩
        refine ⟨by omega, hqU, hfpq1, ?_, ?_, hr0, hrm, hdiv⟩
        · intro c hcL hcU hfp
          rw [hHstep c hcL hcU] at hfp
          by_cases hc : -c ≥ t
          · simp only [hc, ↓reduceIte] at hfp; omega
          · simp only [hc, ↓reduceIte] at hfp; omega
        · intro c₀ hc₀L hc₀U
          rw [hHstep c₀ hc₀L hc₀U]
          by_cases hc : -c₀ ≥ t
          · simp only [hc, ↓reduceIte]; exact hfpq1
          · simp only [hc, ↓reduceIte]; exact hHq

-- ============================================================================
-- 7. General Modulo-m Affine Prefix Monoid A_m & Exact Absorption Criterion
-- ============================================================================

namespace AffMod

theorem comp_act {m : Nat} {hm : 0 < m} (hi lo : AffMod m hm) (c : Nat) :
    (hi.comp lo).act c = hi.act (lo.act c) := by
  simp only [comp, act]
  have h1 : (hi.a * lo.a % m * c + (hi.a * lo.r + hi.r) % m) % m =
            (hi.a * lo.a * c + (hi.a * lo.r + hi.r)) % m := by
    rw [Nat.add_mod, Nat.mul_mod (hi.a * lo.a % m) c, Nat.mod_mod, ← Nat.mul_mod,
        Nat.mod_mod, ← Nat.add_mod]
  have h2 : (hi.a * ((lo.a * c + lo.r) % m) + hi.r) % m =
            (hi.a * (lo.a * c + lo.r) + hi.r) % m := by
    rw [Nat.add_mod, Nat.mul_mod hi.a ((lo.a * c + lo.r) % m), Nat.mod_mod,
        ← Nat.mul_mod, ← Nat.add_mod]
  rw [h1, h2]
  congr 1
  rw [Nat.mul_add, Nat.mul_assoc]
  omega

/-- **Theorem 7a (Exact Modular Base-`b` Tree-Lifting Law):**
Any prefix tree of base-`b` digits of width `w` evaluates in `AffMod m hm` to multiplier `b^w % m`. -/
theorem base_tree_multiplier (m : Nat) (hm : 0 < m) (b : Nat) (t : PrefixTree Nat) :
    (t.eval (baseSlice m hm b)).a = (b ^ t.width) % m := by
  induction t with
  | leaf d => simp [PrefixTree.eval, PrefixTree.width, baseSlice]
  | node lo hi ihlo ihhi =>
    simp only [PrefixTree.eval, PrefixTree.width, PrefixSemigroup.mul, comp]
    rw [ihlo, ihhi]
    rw [Nat.mul_mod (b ^ hi.width % m) (b ^ lo.width % m), Nat.mod_mod, Nat.mod_mod,
        ← Nat.mul_mod, ← Nat.pow_add, Nat.add_comm]

/-- **Theorem 7b (Exact Modulo-`m` Carry-Absorption Law — `∀ m ≥ 1, ∀ b, ∀ w`):**
The width-`w` modulo-`m` affine element `(b^w % m, r)` is completely carry-absorbing
(constant on `{0, ..., m - 1}`) **if and only if** `m ∣ b^w`. -/
theorem mod_m_const_iff_dvd (m : Nat) (hm : 0 < m) (b w r : Nat) (hr : r < m) :
    (∀ c₁ c₂ : Nat, c₁ < m → c₂ < m →
      (baseBlock m hm b w r hr).act c₁ = (baseBlock m hm b w r hr).act c₂) ↔ m ∣ b ^ w := by
  constructor
  · intro hconst
    by_cases hm1 : m = 1
    · subst hm1; exact Nat.one_dvd _
    · have h1lt : 1 < m := by omega
      have h01 := hconst 0 1 hm h1lt
      simp only [baseBlock, act, Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.mod_eq_of_lt hr] at h01
      have ha_lt : b ^ w % m < m := Nat.mod_lt _ hm
      have hzero : b ^ w % m = 0 := by
        by_cases hz : b ^ w % m = 0
        · exact hz
        · by_cases hsum : b ^ w % m + r < m
          · rw [Nat.mod_eq_of_lt hsum] at h01; omega
          · have hsub : (b ^ w % m + r) % m = b ^ w % m + r - m := by
              rw [Nat.mod_eq_sub_mod (by omega : m ≤ b ^ w % m + r), Nat.mod_eq_of_lt (by omega)]
            rw [hsub] at h01; omega
      exact Nat.dvd_of_mod_eq_zero hzero
  · intro hdvd c₁ c₂ _ _
    have hzero : b ^ w % m = 0 := Nat.mod_eq_zero_of_dvd hdvd
    simp [baseBlock, act, hzero]

/-- Sharpness Corollary: For any odd modulus `m > 1`, base-2 remainder-carry NEVER absorbs
at any word width `w : Nat`. -/
theorem odd_modulus_never_absorbs (m : Nat) (hm1 : 1 < m) (hodd : m % 2 = 1)
    (w r : Nat) (hr : r < m) :
    ¬ (∀ c₁ c₂ : Nat, c₁ < m → c₂ < m →
      (baseBlock m (by omega) 2 w r hr).act c₁ = (baseBlock m (by omega) 2 w r hr).act c₂) := by
  rw [mod_m_const_iff_dvd m (by omega) 2 w r hr]
  intro hdvd
  have hcop : Nat.Coprime m 2 := by
    unfold Nat.Coprime
    rw [Nat.gcd_comm]
    have h2 : Nat.gcd 2 m = Nat.gcd (m % 2) 2 := by rw [Nat.gcd_rec, Nat.gcd_comm]
    rw [h2, hodd]
    rfl
  have hcopw : Nat.Coprime m (2 ^ w) := Nat.Coprime.pow_right w hcop
  have hg : Nat.gcd m (2 ^ w) = m := Nat.gcd_eq_left hdvd
  rw [hcopw] at hg
  omega

end AffMod

section NonVacuityWitnesses


/-- Witness 1: 3-input binary addition (`w = 4`), balanced vs left-ripple prefix trees
agree and collapse faithfully in the 7-element semigroup `T_[0, 2]`:
- Resonant pattern `[2, 2, 2, 0]` propagates as `step 0 2`.
- Non-resonant pattern `[2, 2, 0, 2]` absorbs completely to `const 1`. -/
example :
    let d0 : DivElem := ⟨2, by omega, 2⟩
    let d1 : DivElem := ⟨2, by omega, 2⟩
    let d2 : DivElem := ⟨2, by omega, 2⟩
    let d3 : DivElem := ⟨2, by omega, 0⟩
    let tBal : PrefixTree DivElem := .node (.node (.leaf d0) (.leaf d1)) (.node (.leaf d2) (.leaf d3))
    let tRip : PrefixTree DivElem := .node (.node (.node (.leaf d0) (.leaf d1)) (.leaf d2)) (.leaf d3)
    let tAbs : PrefixTree DivElem := .node (.node (.leaf d0) (.leaf d1)) (.node (.leaf d3) (.leaf d2))
    tBal.eval (collapse 0 2) = tRip.eval (collapse 0 2) ∧
    tBal.eval (collapse 0 2) = .step 0 2 ∧
    tAbs.eval (collapse 0 2) = .const 1 ∧
    (ThreshElem.enumBounded 0 3).length = 7 := by
  decide

/-- Witness 2: Signed 3-input `x + y - z` (`L = -1, U = 1`, width 3) — non-resonant
pattern `[1, 0, 2]` absorbs carry completely to `const 0`, while resonant `[0, 1, 3]`
propagates as `step 0 1`. -/
example :
    let tAbs : PrefixTree Nat := .node (.leaf 1) (.node (.leaf 0) (.leaf 2))
    let tProp : PrefixTree Nat := .node (.leaf 0) (.node (.leaf 1) (.leaf 3))
    tAbs.eval encSigned3Bit = .const 0 ∧ BitResonant3 tAbs.fringe = false ∧
    tProp.eval encSigned3Bit = .step 0 1 ∧ BitResonant3 tProp.fringe = true := by
  decide

/-- Witness 3: Exact 3-input width-3 resonance counts (`2^4 = 16` digit strings, `2*4^3 = 128` triples). -/
example :
    ((allDigits3 3).filter BitResonant3).length = 16 ∧
    sumWeights3 ((allDigits3 3).filter BitResonant3) = 128 := by
  exact ⟨three_input_resonant_digit_count 3 (by omega),
         three_input_resonant_triple_count 3 (by omega)⟩

/-- Witness 4: Non-vacuity of `crandall_feedback_dichotomy` on Crandall modulus `m = 2^8 - 19 = 237`
with `L = 0, U = 2` (`M = 256 ≥ 19 * 2 = 38`), showing both unique fixed point (`S = 100`)
and dual-fixed-point band (`S = 240 ∈ [237, 255]`). -/
example :
    let d₁ : DivElem := ⟨256, by omega, 100⟩
    let d₂ : DivElem := ⟨256, by omega, 240⟩
    let e₁ := collapse 0 38 d₁
    let e₂ := collapse 0 38 d₂
    e₁ = .const 0 ∧ crandallFixedPoint 19 e₁ = 0 ∧
    e₂ = .step 0 16 ∧ crandallFixedPoint 19 e₂ = 1 ∧
    (19 * 0 + 240 : Int) / 256 = 0 ∧ (19 * 1 + 240 : Int) / 256 = 1 ∧
    (19 * 1 + 240 : Int) % 256 = 3 := by
  decide

/-- Witness 5: Non-vacuity of `fermat_feedback_dichotomy` on Fermat modulus `m = 2^4 + 1 = 17`
(`M = 16, L = -1, U = 1`), showing exact period-2 oscillation `0 ↔ 1` at `S = 16`
and unique fixed point at `S = 10`. -/
example :
    let dOsc : DivElem := ⟨16, by omega, 16⟩
    let dFix : DivElem := ⟨16, by omega, 10⟩
    collapse (-1) 1 dOsc = .step 0 0 ∧
    (-0 + 16 : Int) / 16 = 1 ∧ (-1 + 16 : Int) / 16 = 0 ∧
    collapse (-1) 1 dFix = .const 0 ∧ fermatFixedPoint (collapse (-1) 1 dFix) = 0 := by
  decide

/-- Witness 6: Modulo-`m` absorption (`m = 8, b = 2, w = 3`) vs non-absorption (`m = 5, b = 2, ∀ w`). -/
example :
    (∀ c₁ c₂ : Nat, c₁ < 8 → c₂ < 8 →
      (AffMod.baseBlock 8 (by omega) 2 3 5 (by omega)).act c₁ =
      (AffMod.baseBlock 8 (by omega) 2 3 5 (by omega)).act c₂) ∧
    (∀ w : Nat, ¬ ∀ c₁ c₂ : Nat, c₁ < 5 → c₂ < 5 →
      (AffMod.baseBlock 5 (by omega) 2 w 2 (by omega)).act c₁ =
      (AffMod.baseBlock 5 (by omega) 2 w 2 (by omega)).act c₂) := by
  exact ⟨(AffMod.mod_m_const_iff_dvd 8 (by omega) 2 3 5 (by omega)).mpr (by decide),
         fun w => AffMod.odd_modulus_never_absorbs 5 (by omega) (by decide) w 2 (by omega)⟩

end NonVacuityWitnesses

end SiliconCarryMonoid
