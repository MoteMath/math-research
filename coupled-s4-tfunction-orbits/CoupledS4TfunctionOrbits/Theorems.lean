/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CoupledS4TfunctionOrbits.Defs

/-!
# Theorems (`coupled-s4-tfunction-orbits`)

Full proofs of the headline infinite theorems of Coupled 2-Variable Reversible T-Function Orbit-Lifting Engine.
-/

namespace CoupledS4TFunction

theorem truncState_liftState {w : Nat} (p : Fiber) (s : State w) :
    truncState (liftState p s) = s := by
  rcases p with ⟨a, b⟩
  rcases s with ⟨x, y⟩
  simp [truncState, liftState]

theorem msbPair_liftState {w : Nat} (p : Fiber) (s : State w) :
    msbPair (liftState p s) = p := by
  rcases p with ⟨a, b⟩
  rcases s with ⟨x, y⟩
  simp [msbPair, liftState]

theorem liftState_eta {w : Nat} (s : State (w + 1)) :
    liftState (msbPair s) (truncState s) = s := by
  rcases s with ⟨x, y⟩
  exact Prod.ext (cons_eta x) (cons_eta y)

theorem liftState_eq_iff {w : Nat} {p₁ p₂ : Fiber} {s₁ s₂ : State w} :
    liftState p₁ s₁ = liftState p₂ s₂ ↔ p₁ = p₂ ∧ s₁ = s₂ := by
  constructor
  · intro h
    have hm := congrArg msbPair h
    have ht := congrArg truncState h
    rw [msbPair_liftState, msbPair_liftState] at hm
    rw [truncState_liftState, truncState_liftState] at ht
    exact ⟨hm, ht⟩
  · rintro ⟨rfl, rfl⟩
    rfl

-- ----------------------------------------------------------------------------
-- Iteration & Exact Minimal Period
-- ----------------------------------------------------------------------------

theorem iter_zero {α : Type} (f : α → α) (x : α) : iter f 0 x = x := rfl

theorem iter_succ {α : Type} (f : α → α) (n : Nat) (x : α) :
    iter f (n + 1) x = f (iter f n x) := rfl

theorem iter_add {α : Type} (f : α → α) (a b : Nat) (x : α) :
    iter f (a + b) x = iter f b (iter f a x) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [Nat.add_succ, iter_succ, iter_succ, ih]

theorem iter_comm_step {α : Type} (f : α → α) (n : Nat) (x : α) :
    iter f n (f x) = f (iter f n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iter_succ, iter_succ, ih]

theorem iter_mul_fixed {α : Type} (f : α → α) (L : Nat) (x : α)
    (hL : iter f L x = x) : ∀ k, iter f (k * L) x = x := by
  intro k
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    rw [Nat.succ_mul, iter_add, ih, hL]

theorem iter_mod_fixed {α : Type} (f : α → α) (L : Nat) (x : α)
    (hL : iter f L x = x) (n : Nat) :
    iter f n x = iter f (n % L) x := by
  have hdiv : n = (n / L) * L + n % L := by
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod n L).symm
  conv => lhs; rw [hdiv]
  rw [iter_add, iter_mul_fixed f L x hL]

theorem dvd_of_iter_eq {α : Type} {f : α → α} {x : α} {L : Nat}
    (hp : IsExactPeriod f x L) {k : Nat} (hk : iter f k x = x) :
    L ∣ k := by
  rcases hp with ⟨hLpos, hLfix, hmin⟩
  have hrem : iter f (k % L) x = x := by
    rw [← iter_mod_fixed f L x hLfix k, hk]
  have hlt : k % L < L := Nat.mod_lt k hLpos
  by_cases hz : k % L = 0
  · exact Nat.dvd_of_mod_eq_zero hz
  · exfalso
    exact hmin (k % L) (Nat.pos_of_ne_zero hz) hlt hrem

theorem iter_inj_lt_period {α : Type} {f : α → α} {x : α} {L : Nat}
    (hp : IsExactPeriod f x L) {i j : Nat} (hi : i < L) (hj : j < L)
    (heq : iter f i x = iter f j x) : i = j := by
  have hstep : ∀ a b, a ≤ b → b < L → iter f a x = iter f b x → a = b := by
    intro a b hab hblt h
    by_cases hba : b - a = 0
    · omega
    · exfalso
      have h1 : iter f (L - a + a) x = iter f (L - a + b) x := by
        rw [Nat.add_comm (L - a) a, Nat.add_comm (L - a) b, iter_add, iter_add, h]
      have h2 : L - a + a = L := by omega
      have h3 : L - a + b = L + (b - a) := by omega
      rw [h2, h3, iter_add, hp.2.1] at h1
      exact hp.2.2 (b - a) (by omega) (by omega) h1.symm
  rcases Nat.le_total i j with hij | hji
  · exact hstep i j hij hj heq
  · exact (hstep j i hji hi heq.symm).symm

-- ----------------------------------------------------------------------------
-- Coupled 2-Variable T-Function & Exact S4 Fiber Monodromy
-- ----------------------------------------------------------------------------

theorem eval_liftState (T : TFunc2) (w : Nat) (p : Fiber) (s : State w) :
    T.eval (w + 1) (liftState p s) = liftState (fiber T w s p) (T.eval w s) := by
  have h := (liftState_eta (T.eval (w + 1) (liftState p s))).symm
  rw [T.compat w (liftState p s), truncState_liftState] at h
  exact h

theorem iter_liftState (T : TFunc2) (w : Nat) (n : Nat) (p : Fiber) (s : State w) :
    iter (T.eval (w + 1)) n (liftState p s) =
      liftState (monodromy T w s n p) (iter (T.eval w) n s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iter_succ, ih, eval_liftState, iter_succ]
    rfl

theorem monodromy_add (T : TFunc2) (w : Nat) (s : State w) (a b : Nat) (p : Fiber) :
    monodromy T w s (a + b) p =
      monodromy T w (iter (T.eval w) a s) b (monodromy T w s a p) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [Nat.add_succ]
    simp only [monodromy]
    rw [ih, iter_add]

theorem monodromy_mul_fixed (T : TFunc2) (w : Nat) (s : State w) (L : Nat)
    (hL : iter (T.eval w) L s = s) (k : Nat) (p : Fiber) :
    monodromy T w s (k * L) p = iter (monodromy T w s L) k p := by
  induction k with
  | zero => simp [monodromy, iter]
  | succ k ih =>
    rw [Nat.succ_mul, monodromy_add, iter_mul_fixed (T.eval w) L s hL k, ih, iter_succ]

/--
  MASTER S4 ORBIT-LIFTING THEOREM:
  For ANY coupled 2-variable T-function T, if base state s at width w has exact
  minimal period L, and MSB pair p has exact minimal period d under the cycle
  monodromy M = monodromy T w s L : Fiber → Fiber, then liftState p s has
  EXACT minimal period d * L at width w + 1.
-/
theorem orbit_lift_exact_period (T : TFunc2) (w : Nat) (s : State w) (L : Nat)
    (p : Fiber) (d : Nat)
    (hBase : IsExactPeriod (T.eval w) s L)
    (hMon : IsExactPeriod (monodromy T w s L) p d) :
    IsExactPeriod (T.eval (w + 1)) (liftState p s) (d * L) := by
  refine ⟨Nat.mul_pos hMon.1 hBase.1, ?_, ?_⟩
  · rw [iter_liftState, monodromy_mul_fixed T w s L hBase.2.1 d p,
        iter_mul_fixed (T.eval w) L s hBase.2.1 d, hMon.2.1]
  · intro k hkpos hklt hfix
    rw [iter_liftState, liftState_eq_iff] at hfix
    have hdvd : L ∣ k := dvd_of_iter_eq hBase hfix.2
    rcases hdvd with ⟨q, rfl⟩
    rw [Nat.mul_comm L q] at hkpos hklt hfix
    have hqpos : 0 < q := by
      cases q with
      | zero => simp at hkpos
      | succ _ => exact Nat.succ_pos _
    have hqlt : q < d := Nat.lt_of_mul_lt_mul_right hklt
    rw [monodromy_mul_fixed T w s L hBase.2.1 q p] at hfix
    exact hMon.2.2 q hqpos hqlt hfix.1

-- ----------------------------------------------------------------------------
-- Complete S4 Lifting Classification Corollaries
-- ----------------------------------------------------------------------------

theorem lift_quadruple (T : TFunc2) (w : Nat) (s : State w) (L : Nat)
    (hBase : IsExactPeriod (T.eval w) s L)
    (h4 : ∀ p : Fiber, IsExactPeriod (monodromy T w s L) p 4) :
    ∀ p : Fiber, IsExactPeriod (T.eval (w + 1)) (liftState p s) (4 * L) :=
  fun p => orbit_lift_exact_period T w s L p 4 hBase (h4 p)

theorem lift_ternary_split (T : TFunc2) (w : Nat) (s : State w) (L : Nat)
    (pFix : Fiber)
    (hBase : IsExactPeriod (T.eval w) s L)
    (hFix : monodromy T w s L pFix = pFix)
    (h3 : ∀ p : Fiber, p ≠ pFix → IsExactPeriod (monodromy T w s L) p 3) :
    IsExactPeriod (T.eval (w + 1)) (liftState pFix s) L ∧
    ∀ p : Fiber, p ≠ pFix → IsExactPeriod (T.eval (w + 1)) (liftState p s) (3 * L) := by
  constructor
  · have h1 : IsExactPeriod (monodromy T w s L) pFix 1 :=
      ⟨Nat.one_pos, hFix, fun k hk1 hk2 => by omega⟩
    have := orbit_lift_exact_period T w s L pFix 1 hBase h1
    simpa using this
  · intro p hp
    exact orbit_lift_exact_period T w s L p 3 hBase (h3 p hp)

theorem lift_double_transposition (T : TFunc2) (w : Nat) (s : State w) (L : Nat)
    (hBase : IsExactPeriod (T.eval w) s L)
    (h2 : ∀ p : Fiber, IsExactPeriod (monodromy T w s L) p 2) :
    ∀ p : Fiber, IsExactPeriod (T.eval (w + 1)) (liftState p s) (2 * L) :=
  fun p => orbit_lift_exact_period T w s L p 2 hBase (h2 p)

-- ----------------------------------------------------------------------------
-- The No-Shear Obstruction Theorem (Pure Translations <= 2^w)
-- ----------------------------------------------------------------------------

theorem pureTranslation_comp {f g : Fiber → Fiber}
    (hf : IsPureTranslation f) (hg : IsPureTranslation g) :
    IsPureTranslation (fun p => f (g p)) := by
  rcases hf with ⟨a₁, b₁, hf⟩
  rcases hg with ⟨a₂, b₂, hg⟩
  refine ⟨xor a₂ a₁, xor b₂ b₁, fun ⟨x, y⟩ => ?_⟩
  change f (g (x, y)) = (xor x (xor a₂ a₁), xor y (xor b₂ b₁))
  rw [hg (x, y), hf]
  cases x <;> cases y <;> cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> rfl

theorem pureTranslation_monodromy (T : TFunc2) (w : Nat)
    (hT : ∀ s : State w, IsPureTranslation (fiber T w s))
    (s : State w) (n : Nat) :
    IsPureTranslation (monodromy T w s n) := by
  induction n with
  | zero => exact ⟨false, false, fun ⟨a, b⟩ => by cases a <;> cases b <;> rfl⟩
  | succ n ih =>
    show IsPureTranslation (fun p => fiber T w (iter (T.eval w) n s) (monodromy T w s n p))
    exact pureTranslation_comp (hT (iter (T.eval w) n s)) ih

theorem pureTranslation_sq_id {f : Fiber → Fiber} (hf : IsPureTranslation f) (p : Fiber) :
    f (f p) = p := by
  rcases hf with ⟨a, b, hf⟩
  rcases p with ⟨x, y⟩
  rw [hf, hf]
  cases x <;> cases y <;> cases a <;> cases b <;> rfl

/--
  NO-SHEAR OBSTRUCTION THEOREM:
  If every bit-slice fiber of a coupled 2-variable T-function T is a pure
  translation (no cross-bit shear/rotation in S4), then for EVERY width w and
  EVERY state s ∈ (BitVec w)^2, T_w^(2^w)(s) = s.
  Consequently, NO pure-translation coupled 2-variable T-function can EVER reach
  period 2^(2w) (or even 3^w) for any w >= 1!
-/
theorem no_shear_period_bound (T : TFunc2)
    (hNoShear : ∀ w (s : State w), IsPureTranslation (fiber T w s)) :
    ∀ w (s : State w), iter (T.eval w) (2 ^ w) s = s := by
  intro w
  induction w with
  | zero =>
    intro ⟨x, y⟩
    exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  | succ w ih =>
    intro s
    rw [← liftState_eta s]
    have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, iter_liftState,
        monodromy_mul_fixed T w (truncState s) (2 ^ w) (ih (truncState s)) 2 (msbPair s),
        iter_mul_fixed (T.eval w) (2 ^ w) (truncState s) (ih (truncState s)) 2]
    have hpt := pureTranslation_monodromy T w (hNoShear w) (truncState s) (2 ^ w)
    have hsq : iter (monodromy T w (truncState s) (2 ^ w)) 2 (msbPair s) = msbPair s :=
      pureTranslation_sq_id hpt (msbPair s)
    rw [hsq]

theorem no_shear_never_full_period (T : TFunc2)
    (hNoShear : ∀ w (s : State w), IsPureTranslation (fiber T w s))
    (w : Nat) (hw : 1 ≤ w) (s : State w) :
    ¬ IsExactPeriod (T.eval w) s (4 ^ w) := by
  intro hfull
  have hlt : 2 ^ w < 4 ^ w := by
    have h4 : 4 ^ w = 2 ^ w * 2 ^ w := by rw [← Nat.mul_pow]
    have hge2 : 2 ≤ 2 ^ w := by
      have : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
      omega
    have hpos : 0 < 2 ^ w := Nat.pow_pos (by omega)
    rw [h4]
    calc 2 ^ w = 2 ^ w * 1 := (Nat.mul_one _).symm
      _ < 2 ^ w * 2 ^ w := Nat.mul_lt_mul_of_pos_left (by omega) hpos
  exact hfull.2.2 (2 ^ w) (Nat.pow_pos (by omega)) hlt (no_shear_period_bound T hNoShear w s)

-- ----------------------------------------------------------------------------
-- The D4 Sylow-2 Borelian Cocycle Decoupling Engine
-- ----------------------------------------------------------------------------

theorem D4Elem.apply_id (p : Fiber) : D4Elem.id.apply p = p := by
  rcases p with ⟨x, y⟩
  cases x <;> cases y <;> rfl

theorem D4Elem.apply_comp (e₂ e₁ : D4Elem) (p : Fiber) :
    (D4Elem.comp e₂ e₁).apply p = e₂.apply (e₁.apply p) := by
  rcases e₁ with ⟨l1, a1, b1⟩
  rcases e₂ with ⟨l2, a2, b2⟩
  rcases p with ⟨x, y⟩
  cases l1 <;> cases a1 <;> cases b1 <;> cases l2 <;> cases a2 <;> cases b2 <;>
    cases x <;> cases y <;> rfl

/--
  D4 MONODROMY DECOUPLING MIRACLE:
  An element e = (lam, alpha, beta) ∈ D4 is a 4-cycle on Fiber IF AND ONLY IF
  lam = true ∧ beta = true — COMPLETELY INDEPENDENT of the nonlinear cocycle alpha!
-/
theorem D4Elem.is_4cycle_iff (e : D4Elem) :
    (∀ p : Fiber, IsExactPeriod e.apply p 4) ↔ e.lam = true ∧ e.beta = true := by
  rcases e with ⟨l, a, b⟩
  constructor
  · intro h
    have h0 := h (false, false)
    cases l <;> cases a <;> cases b
    · exfalso; exact h0.2.2 1 (by omega) (by omega) rfl
    · exfalso; exact h0.2.2 2 (by omega) (by omega) rfl
    · exfalso; exact h0.2.2 2 (by omega) (by omega) rfl
    · exfalso; exact h0.2.2 2 (by omega) (by omega) rfl
    · exfalso; exact h0.2.2 1 (by omega) (by omega) rfl
    · exact ⟨rfl, rfl⟩
    · exfalso; exact h0.2.2 2 (by omega) (by omega) rfl
    · exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩ ⟨x, y⟩
    refine ⟨by omega, ?_, ?_⟩
    · cases a <;> cases x <;> cases y <;> rfl
    · intro k hk1 hk4
      have : k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases this with rfl | rfl | rfl <;> (cases a <;> cases x <;> cases y <;> decide)

-- ----------------------------------------------------------------------------
-- Exact Finite Enumeration of BitVec w × BitVec w & XOR-Sum Machinery
-- ----------------------------------------------------------------------------

theorem allBitVecs_length (w : Nat) : (allBitVecs w).length = 2 ^ w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp [allBitVecs, ih, Nat.pow_succ, Nat.mul_two]

theorem mem_allBitVecs {w : Nat} (x : BitVec w) : x ∈ allBitVecs w := by
  induction w with
  | zero =>
    have hx : x = 0#0 := Subsingleton.elim _ _
    subst hx
    simp [allBitVecs]
  | succ w ih =>
    rw [← cons_eta x]
    cases h : x.getLsbD w
    · simp only [allBitVecs, List.mem_append, List.mem_map]
      left
      exact ⟨x.setWidth w, ih _, rfl⟩
    · simp only [allBitVecs, List.mem_append, List.mem_map]
      right
      exact ⟨x.setWidth w, ih _, rfl⟩

theorem nodup_map_inj {α β : Type} {f : α → β} {l : List α}
    (hf : ∀ a b, f a = f b → a = b) (hl : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih hl.2⟩
    rintro ⟨b, hb, heq⟩
    exact hl.1 (hf b a heq ▸ hb)

theorem nodup_allBitVecs (w : Nat) : (allBitVecs w).Nodup := by
  induction w with
  | zero => simp [allBitVecs]
  | succ w ih =>
    simp only [allBitVecs, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact nodup_map_inj (fun a b h => by
        have := congrArg (BitVec.setWidth w) h
        simpa using this) ih
    · exact nodup_map_inj (fun a b h => by
        have := congrArg (BitVec.setWidth w) h
        simpa using this) ih
    · intro u hu v hv heq
      rw [List.mem_map] at hu hv
      rcases hu with ⟨a, _, rfl⟩
      rcases hv with ⟨b, _, rfl⟩
      have hmsb := congrArg (fun z : BitVec (w + 1) => z.getLsbD w) heq
      simp at hmsb

theorem allStates_length (w : Nat) : (allStates w).length = 4 ^ w := by
  simp only [allStates, List.length_flatMap, List.length_map, allBitVecs_length]
  have hsum : ∀ (l : List (BitVec w)) (c : Nat),
      (l.map (fun _ => c)).sum = l.length * c := by
    intro l c
    induction l with
    | nil => simp
    | cons _ t ih => simp [ih, Nat.succ_mul, Nat.add_comm]
  rw [hsum, allBitVecs_length]
  have h4 : 4 ^ w = 2 ^ w * 2 ^ w := by rw [← Nat.mul_pow]
  omega

theorem mem_allStates {w : Nat} (s : State w) : s ∈ allStates w := by
  rcases s with ⟨x, y⟩
  simp only [allStates, List.mem_flatMap, List.mem_map]
  exact ⟨x, mem_allBitVecs x, y, mem_allBitVecs y, rfl⟩

theorem nodup_flatMap_aux {α β : Type} {l : List α} {g : α → List β}
    (hl : l.Nodup) (hg : ∀ a ∈ l, (g a).Nodup)
    (hdisj : ∀ a₁ ∈ l, ∀ a₂ ∈ l, a₁ ≠ a₂ → ∀ b, b ∈ g a₁ → b ∉ g a₂) :
    (l.flatMap g).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons, List.nodup_append]
    rw [List.nodup_cons] at hl
    refine ⟨hg a (by simp), ih hl.2 (fun x hx => hg x (by simp [hx]))
      (fun a₁ h1 a₂ h2 hne => hdisj a₁ (by simp [h1]) a₂ (by simp [h2]) hne), ?_⟩
    intro b hb₁ b₂ hb₂ heq
    subst heq
    rw [List.mem_flatMap] at hb₂
    rcases hb₂ with ⟨a₂, ha₂, hb₂⟩
    have hne : a ≠ a₂ := fun h => hl.1 (h ▸ ha₂)
    exact hdisj a (by simp) a₂ (by simp [ha₂]) hne b hb₁ hb₂

theorem nodup_allStates (w : Nat) : (allStates w).Nodup := by
  apply nodup_flatMap_aux (nodup_allBitVecs w)
  · intro x _
    exact nodup_map_inj (fun a b h => (Prod.mk.inj h).2) (nodup_allBitVecs w)
  · intro x₁ _ x₂ _ hne s h1 h2
    rw [List.mem_map] at h1 h2
    rcases h1 with ⟨y₁, _, rfl⟩
    rcases h2 with ⟨y₂, _, heq⟩
    exact hne (Prod.mk.inj heq).1.symm

-- XOR-sum over a List (commutative & associative in F2!)

theorem xorList_append {α : Type} (f : α → Bool) (l₁ l₂ : List α) :
    xorList f (l₁ ++ l₂) = xor (xorList f l₁) (xorList f l₂) := by
  induction l₁ with
  | nil => simp [xorList]
  | cons a t ih =>
    simp only [List.cons_append, xorList, ih]
    cases f a <;> cases xorList f t <;> cases xorList f l₂ <;> rfl

theorem xorList_perm {α : Type} (f : α → Bool) {l₁ l₂ : List α} (hp : l₁.Perm l₂) :
    xorList f l₁ = xorList f l₂ := by
  induction hp with
  | nil => rfl
  | cons x _ ih => simp [xorList, ih]
  | swap x y l =>
    simp only [xorList]
    cases f x <;> cases f y <;> cases xorList f l <;> rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem xorList_map {α β : Type} (f : β → Bool) (g : α → β) (l : List α) :
    xorList f (l.map g) = xorList (fun a => f (g a)) l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [xorList, ih]

theorem xorList_xor {α : Type} (f g : α → Bool) (l : List α) :
    xorList (fun a => xor (f a) (g a)) l = xor (xorList f l) (xorList g l) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [xorList, ih]
    cases f a <;> cases g a <;> cases xorList f t <;> cases xorList g t <;> rfl

theorem xorList_all_false {α : Type} (f : α → Bool) (l : List α)
    (h : ∀ x ∈ l, f x = false) : xorList f l = false := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [xorList, h a (by simp), ih (fun x hx => h x (by simp [hx]))]
    rfl

-- Two Nodup lists of equal length with subset inclusion are Perm!

theorem perm_of_nodup_subset_len {α : Type} [DecidableEq α] {l₁ l₂ : List α}
    (h1 : l₁.Nodup) (h2 : l₂.Nodup) (hlen : l₁.length = l₂.length)
    (hsub : ∀ x, x ∈ l₁ → x ∈ l₂) : l₁.Perm l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact List.Perm.nil
    | cons _ _ => simp at hlen
  | cons a t ih =>
    rw [List.nodup_cons] at h1
    have ha₂ : a ∈ l₂ := hsub a (by simp)
    have hperm_a : l₂.Perm (a :: l₂.erase a) := List.perm_cons_erase ha₂
    have hnd2 : (a :: l₂.erase a).Nodup := hperm_a.nodup_iff.mp h2
    rw [List.nodup_cons] at hnd2
    have hlen_e : t.length = (l₂.erase a).length := by
      have hlen2 := hperm_a.length_eq
      simp at hlen hlen2
      omega
    have hsub_e : ∀ x, x ∈ t → x ∈ l₂.erase a := by
      intro x hx
      have hne : x ≠ a := fun h => h1.1 (h ▸ hx)
      have hx2 : x ∈ a :: l₂.erase a := hperm_a.subset (hsub x (by simp [hx]))
      rcases List.mem_cons.mp hx2 with rfl | hmem
      · exact absurd rfl hne
      · exact hmem
    have iht := ih h1.2 hnd2.2 hlen_e hsub_e
    exact (iht.cons a).trans hperm_a.symm

-- Orbit list of length L starting at s0

theorem orbitList_length {α : Type} (f : α → α) (s0 : α) (n : Nat) :
    (orbitList f s0 n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [orbitList, ih]

theorem mem_orbitList_iff {α : Type} (f : α → α) (s0 : α) (n : Nat) (x : α) :
    x ∈ orbitList f s0 n ↔ ∃ k < n, iter f k s0 = x := by
  induction n with
  | zero => simp [orbitList]
  | succ n ih =>
    simp only [orbitList, List.mem_append, List.mem_singleton, ih]
    constructor
    · rintro (⟨k, hk, rfl⟩ | rfl)
      · exact ⟨k, Nat.lt_succ_of_lt hk, rfl⟩
      · exact ⟨n, Nat.lt_succ_self n, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · left; exact ⟨k, hlt, rfl⟩
      · right; rfl

theorem nodup_orbitList {α : Type} {f : α → α} {s0 : α} {L : Nat}
    (hp : IsExactPeriod f s0 L) : ∀ n ≤ L, (orbitList f s0 n).Nodup := by
  intro n hn
  induction n with
  | zero => simp [orbitList]
  | succ n ih =>
    simp only [orbitList, List.nodup_append]
    refine ⟨ih (by omega), by simp, ?_⟩
    intro a ha b hb heq
    rw [List.mem_singleton] at hb
    subst hb; subst heq
    rw [mem_orbitList_iff] at ha
    rcases ha with ⟨k, hk, heqk⟩
    have := iter_inj_lt_period hp (by omega : k < L) (by omega : n < L) heqk
    omega

/-- Any state on a full-period 4^w orbit visits ALL of allStates w exactly once! -/
theorem orbitList_perm_allStates {w : Nat} {f : State w → State w} {s0 : State w}
    (hp : IsExactPeriod f s0 (4 ^ w)) :
    (orbitList f s0 (4 ^ w)).Perm (allStates w) := by
  apply perm_of_nodup_subset_len (nodup_orbitList hp (4 ^ w) (Nat.le_refl _))
    (nodup_allStates w)
  · rw [orbitList_length, allStates_length]
  · intro x _
    exact mem_allStates x

/-- If ONE state has exact period 4^w, then EVERY state has exact period 4^w! -/
theorem full_period_all_states {w : Nat} {f : State w → State w} {s0 : State w}
    (hp : IsExactPeriod f s0 (4 ^ w)) :
    ∀ s : State w, IsExactPeriod f s (4 ^ w) := by
  intro s
  have hmem : s ∈ orbitList f s0 (4 ^ w) :=
    (orbitList_perm_allStates hp).symm.subset (mem_allStates s)
  rw [mem_orbitList_iff] at hmem
  rcases hmem with ⟨j, _, rfl⟩
  refine ⟨hp.1, ?_, ?_⟩
  · rw [← iter_add, Nat.add_comm, iter_add, hp.2.1]
  · intro k hkpos hklt hfix
    rw [← iter_add] at hfix
    have hmod1 := iter_mod_fixed f (4 ^ w) s0 hp.2.1 (j + k)
    have hmod2 := iter_mod_fixed f (4 ^ w) s0 hp.2.1 j
    rw [hfix] at hmod1
    have heq := iter_inj_lt_period hp (Nat.mod_lt _ hp.1) (Nat.mod_lt _ hp.1) (hmod1.symm.trans hmod2)
    have hlt : j % 4 ^ w < 4 ^ w := Nat.mod_lt _ hp.1
    have hmod_add : (j + k) % 4 ^ w = (j % 4 ^ w + k) % 4 ^ w := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt hklt]
    rw [hmod_add] at heq
    by_cases hsum : j % 4 ^ w + k < 4 ^ w
    · rw [Nat.mod_eq_of_lt hsum] at heq; omega
    · have hsub : (j % 4 ^ w + k) % 4 ^ w = j % 4 ^ w + k - 4 ^ w := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hsub] at heq; omega

/-- Any full-period 4^w map on State w is bijective! -/
theorem bijective_of_full_period {w : Nat} {f : State w → State w} {s0 : State w}
    (hp : IsExactPeriod f s0 (4 ^ w)) :
    (∀ a b, f a = f b → a = b) ∧ (∀ y, ∃ x, f x = y) := by
  have hall := full_period_all_states hp
  have hpow : 4 ^ w = (4 ^ w - 1) + 1 := by
    have := hp.1; omega
  constructor
  · intro a b hab
    have ha := (hall a).2.1
    have hb := (hall b).2.1
    have h1 : iter f (4 ^ w - 1) (f a) = a := by
      rw [iter_comm_step, ← iter_succ f (4 ^ w - 1) a, ← hpow, ha]
    have h2 : iter f (4 ^ w - 1) (f b) = b := by
      rw [iter_comm_step, ← iter_succ f (4 ^ w - 1) b, ← hpow, hb]
    rw [← h1, hab, h2]
  · intro y
    have hy := (hall y).2.1
    refine ⟨iter f (4 ^ w - 1) y, ?_⟩
    rw [← iter_succ f (4 ^ w - 1) y, ← hpow, hy]

-- ----------------------------------------------------------------------------
-- D4 Inductive Full-Period 2^(2w) Lifting Engine
-- ----------------------------------------------------------------------------

theorem d4Monodromy_apply (T : TFunc2) (w : Nat)
    (lam alpha beta : State w → Bool)
    (hFiber : ∀ s p, fiber T w s p = (D4Elem.mk (lam s) (alpha s) (beta s)).apply p)
    (s : State w) (n : Nat) (p : Fiber) :
    monodromy T w s n p = (d4Monodromy T w lam alpha beta s n).apply p := by
  induction n with
  | zero => simp [monodromy, d4Monodromy, D4Elem.apply_id]
  | succ n ih =>
    simp only [monodromy, d4Monodromy]
    rw [ih, hFiber, ← D4Elem.apply_comp]

theorem d4Monodromy_lam (T : TFunc2) (w : Nat)
    (lam alpha beta : State w → Bool) (s : State w) (n : Nat) :
    (d4Monodromy T w lam alpha beta s n).lam = xorList lam (orbitList (T.eval w) s n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [d4Monodromy, D4Elem.comp, orbitList, xorList_append, xorList, ih]
    cases xorList lam (orbitList (T.eval w) s n) <;> cases lam (iter (T.eval w) n s) <;> rfl

theorem d4Monodromy_beta (T : TFunc2) (w : Nat)
    (lam alpha beta : State w → Bool) (s : State w) (n : Nat) :
    (d4Monodromy T w lam alpha beta s n).beta = xorList beta (orbitList (T.eval w) s n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [d4Monodromy, D4Elem.comp, orbitList, xorList_append, xorList, ih]
    cases xorList beta (orbitList (T.eval w) s n) <;> cases beta (iter (T.eval w) n s) <;> rfl

/--
  D4 FULL-PERIOD 2^(2w) INDUCTIVE LIFTING ENGINE:
  If T is a D4-fibered coupled 2-variable T-function whose local shear lam_w and
  y-flip beta_w BOTH have odd XOR-sum over all 4^w states of (BitVec w)^2 for every
  w >= 0, then for EVERY w >= 0 and EVERY state s ∈ (BitVec w)^2, s has EXACT
  minimal period 4^w = 2^(2w) (single full cycle)!
-/
theorem full_period_of_D4_parity (T : TFunc2)
    (lam alpha beta : ∀ w, State w → Bool)
    (hFiber : ∀ w s p, fiber T w s p = (D4Elem.mk (lam w s) (alpha w s) (beta w s)).apply p)
    (hLam : ∀ w, xorList (lam w) (allStates w) = true)
    (hBeta : ∀ w, xorList (beta w) (allStates w) = true) :
    ∀ w (s : State w), IsExactPeriod (T.eval w) s (4 ^ w) := by
  intro w
  induction w with
  | zero =>
    intro s
    refine ⟨by omega, ?_, fun k hk1 hk2 => by omega⟩
    cases s with | mk x y =>
    cases T.eval 0 (x, y) with | mk x' y' =>
    exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  | succ w ih =>
    have hBase : IsExactPeriod (T.eval w) (0#w, 0#w) (4 ^ w) := ih (0#w, 0#w)
    let M := d4Monodromy T w (lam w) (alpha w) (beta w) (0#w, 0#w) (4 ^ w)
    have hperm := orbitList_perm_allStates hBase
    have hMlam : M.lam = true := by
      show (d4Monodromy T w (lam w) (alpha w) (beta w) (0#w, 0#w) (4 ^ w)).lam = true
      rw [d4Monodromy_lam, xorList_perm (lam w) hperm, hLam w]
    have hMbeta : M.beta = true := by
      show (d4Monodromy T w (lam w) (alpha w) (beta w) (0#w, 0#w) (4 ^ w)).beta = true
      rw [d4Monodromy_beta, xorList_perm (beta w) hperm, hBeta w]
    have h4 : ∀ p : Fiber, IsExactPeriod (monodromy T w (0#w, 0#w) (4 ^ w)) p 4 := by
      intro p
      have hfun : monodromy T w (0#w, 0#w) (4 ^ w) = M.apply :=
        funext (d4Monodromy_apply T w (lam w) (alpha w) (beta w) (hFiber w) (0#w, 0#w) (4 ^ w))
      rw [hfun]
      exact (D4Elem.is_4cycle_iff M).mpr ⟨hMlam, hMbeta⟩ p
    have hLift : IsExactPeriod (T.eval (w + 1)) (liftState (false, false) (0#w, 0#w)) (4 ^ (w + 1)) := by
      have h := lift_quadruple T w (0#w, 0#w) (4 ^ w) hBase h4 (false, false)
      have hpow : 4 * 4 ^ w = 4 ^ (w + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      rwa [hpow] at h
    exact full_period_all_states hLift

-- ----------------------------------------------------------------------------
-- Pairing-Involution XOR-Parity Engine
-- ----------------------------------------------------------------------------

theorem xorList_unique_true {α : Type} [DecidableEq α] (f : α → Bool) (l : List α)
    (hnodup : l.Nodup) (sStar : α) (hmem : sStar ∈ l)
    (hTrue : f sStar = true) (hOther : ∀ s ∈ l, s ≠ sStar → f s = false) :
    xorList f l = true := by
  have hperm : l.Perm (sStar :: l.erase sStar) := List.perm_cons_erase hmem
  rw [xorList_perm f hperm, xorList, hTrue]
  have hnd : (sStar :: l.erase sStar).Nodup := hperm.nodup_iff.mp hnodup
  rw [List.nodup_cons] at hnd
  have hrest : xorList f (l.erase sStar) = false := by
    apply xorList_all_false
    intro s hs
    have hne : s ≠ sStar := fun h => hnd.1 (h ▸ hs)
    exact hOther s (List.mem_of_mem_erase hs) hne
  rw [hrest]; rfl

theorem xorList_allBitVecs_succ (w : Nat) (g : BitVec (w + 1) → Bool) :
    xorList g (allBitVecs (w + 1)) =
      xorList (fun x => xor (g (BitVec.cons false x)) (g (BitVec.cons true x))) (allBitVecs w) := by
  simp only [allBitVecs, xorList_append, xorList_map, xorList_xor]

theorem nodup_halfStates (w : Nat) : (halfStates w).Nodup := by
  apply nodup_flatMap_aux (nodup_allBitVecs w)
  · intro x _
    exact nodup_map_inj (fun a b h => (Prod.mk.inj h).2) (nodup_allBitVecs (w + 1))
  · intro x₁ _ x₂ _ hne s h1 h2
    rw [List.mem_map] at h1 h2
    rcases h1 with ⟨y₁, _, rfl⟩
    rcases h2 with ⟨y₂, _, heq⟩
    exact hne (Prod.mk.inj heq).1.symm

theorem mem_halfStates {w : Nat} (s : BitVec w × BitVec (w + 1)) : s ∈ halfStates w := by
  rcases s with ⟨x, y⟩
  simp only [halfStates, List.mem_flatMap, List.mem_map]
  exact ⟨x, mem_allBitVecs x, y, mem_allBitVecs y, rfl⟩

/-- Pairing-Involution XOR-Sum Lemma on State (w+1):
    Flipping bit w of x pairs (cons false x, y) with (cons true x, y). -/
theorem xorList_allStates_x_pair (w : Nat) (f : State (w + 1) → Bool) :
    xorList f (allStates (w + 1)) =
      xorList (fun s : BitVec w × BitVec (w + 1) =>
        xor (f (BitVec.cons false s.1, s.2)) (f (BitVec.cons true s.1, s.2)))
        (halfStates w) := by
  have hflat : ∀ (lx : List (BitVec (w + 1))) (ly : List (BitVec (w + 1))),
      xorList f (lx.flatMap (fun x => ly.map (fun y => (x, y)))) =
      xorList (fun x => xorList (fun y => f (x, y)) ly) lx := by
    intro lx ly
    induction lx with
    | nil => rfl
    | cons x t ih =>
      simp only [List.flatMap_cons, xorList_append, xorList_map, xorList, ih]
  have hflat2 : ∀ (lx : List (BitVec w)) (ly : List (BitVec (w + 1)))
      (h : BitVec w × BitVec (w + 1) → Bool),
      xorList h (lx.flatMap (fun x => ly.map (fun y => (x, y)))) =
      xorList (fun x => xorList (fun y => h (x, y)) ly) lx := by
    intro lx ly h
    induction lx with
    | nil => rfl
    | cons x t ih =>
      simp only [List.flatMap_cons, xorList_append, xorList_map, xorList, ih]
  rw [allStates, hflat, xorList_allBitVecs_succ, halfStates, hflat2]
  congr 1
  funext x
  rw [xorList_xor]

-- ============================================================================
-- PART 2: INFINITE THEOREM FAMILY I — UNIVERSAL NONLINEAR FULL-PERIOD 2^(2w)
-- ============================================================================

theorem nat_one_and_bne_zero (m : Nat) :
    (1 &&& m != 0) = decide (m % 2 = 1) := by
  rw [Nat.and_comm, Nat.and_one_is_mod]
  have hlt : m % 2 < 2 := Nat.mod_lt m (by omega)
  cases h : m % 2 with
  | zero => rfl
  | succ k =>
    have : k = 0 := by omega
    subst this; rfl

theorem getLsbD_eq_decide_div {w : Nat} (z : BitVec (w + 1)) :
    z.getLsbD w = decide ((z.toNat / 2 ^ w) % 2 = 1) := by
  rw [BitVec.getLsbD]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
  exact nat_one_and_bne_zero _

theorem two_pow_or_eq_add {w n : Nat} (hn : n < 2 ^ w) :
    (2 ^ w ||| n) = 2 ^ w + n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, nat_one_and_bne_zero]
  have hpos : 0 < 2 ^ i := Nat.pow_pos (by omega)
  by_cases hlt : i < w
  · have hne : ¬ (w = i) := by omega
    simp only [hne, decide_false, Bool.false_or]
    have hsplit : 2 ^ w = 2 ^ i * (2 * 2 ^ (w - i - 1)) := by
      have : w = i + (1 + (w - i - 1)) := by omega
      conv => lhs; rw [this]
      rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]
    rw [hsplit, Nat.mul_add_div hpos]
    have : (2 * 2 ^ (w - i - 1) + n / 2 ^ i) % 2 = (n / 2 ^ i) % 2 := by omega
    rw [this]
  · by_cases heq : i = w
    · subst heq
      simp only [decide_true, Bool.true_or]
      rw [Nat.add_div_left _ hpos, Nat.div_eq_of_lt hn]
      rfl
    · have hgt : w < i := by omega
      have hne : ¬ (w = i) := by omega
      simp only [hne, decide_false, Bool.false_or]
      have h2i : 2 ^ (w + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
      have h1 : n / 2 ^ i = 0 := Nat.div_eq_of_lt (by omega)
      have h2 : (2 ^ w + n) / 2 ^ i = 0 := Nat.div_eq_of_lt (by omega)
      rw [h1, h2]

theorem toNat_cons_eq {w : Nat} (b : Bool) (x : BitVec w) :
    (BitVec.cons b x).toNat = (if b then 2 ^ w else 0) + x.toNat := by
  cases b with
  | false => simp [BitVec.toNat_cons]
  | true =>
    have h := BitVec.toNat_cons true x
    simp only [Bool.toNat_true, Nat.shiftLeft_eq, Nat.one_mul] at h
    rw [h, two_pow_or_eq_add x.isLt]
    simp

/-- Adding a BitVec (w+1) to BitVec.cons a x flips bit w linearly in a! -/
theorem getLsbD_add_cons {w : Nat} (b : Bool) (x : BitVec w) (y : BitVec (w + 1)) :
    (BitVec.cons b x + y).getLsbD w =
      xor b ((BitVec.cons false x + y).getLsbD w) := by
  rw [getLsbD_eq_decide_div, getLsbD_eq_decide_div]
  simp only [BitVec.toNat_add, toNat_cons_eq]
  have hx : x.toNat < 2 ^ w := x.isLt
  have hy : y.toNat < 2 ^ (w + 1) := y.isLt
  have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  have hpos : 0 < 2 ^ w := Nat.pow_pos (by omega)
  cases b with
  | false => simp
  | true =>
    simp only [↓reduceIte, Bool.false_eq_true, Nat.zero_add, Bool.true_xor]
    rw [Nat.add_assoc]
    let S := x.toNat + y.toNat
    change decide ((2 ^ w + S) % 2 ^ (w + 1) / 2 ^ w % 2 = 1) =
           !decide (S % 2 ^ (w + 1) / 2 ^ w % 2 = 1)
    have hSlt : S < 3 * 2 ^ w := by omega
    by_cases h1 : S < 2 ^ w
    · have hA : (2 ^ w + S) % 2 ^ (w + 1) = 2 ^ w + S := Nat.mod_eq_of_lt (by omega)
      have hB : S % 2 ^ (w + 1) = S := Nat.mod_eq_of_lt (by omega)
      have hdA : (2 ^ w + S) / 2 ^ w = 1 := by
        rw [Nat.add_div_left _ hpos, Nat.div_eq_of_lt h1]
      have hdB : S / 2 ^ w = 0 := Nat.div_eq_of_lt h1
      rw [hA, hB, hdA, hdB]; decide
    · by_cases h2 : S < 2 * 2 ^ w
      · have hA : (2 ^ w + S) % 2 ^ (w + 1) = S - 2 ^ w := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        have hB : S % 2 ^ (w + 1) = S := Nat.mod_eq_of_lt (by omega)
        have hdA : (S - 2 ^ w) / 2 ^ w = 0 := Nat.div_eq_of_lt (by omega)
        have hdB : S / 2 ^ w = 1 := by
          have : S = 2 ^ w + (S - 2 ^ w) := by omega
          rw [this, Nat.add_div_left _ hpos, Nat.div_eq_of_lt (by omega)]
        rw [hA, hB, hdA, hdB]; decide
      · have hA : (2 ^ w + S) % 2 ^ (w + 1) = S - 2 ^ w := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        have hB : S % 2 ^ (w + 1) = S - 2 * 2 ^ w := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        have hdA : (S - 2 ^ w) / 2 ^ w = 1 := by
          have : S - 2 ^ w = 2 ^ w + (S - 2 * 2 ^ w) := by omega
          rw [this, Nat.add_div_left _ hpos, Nat.div_eq_of_lt (by omega)]
        have hdB : (S - 2 * 2 ^ w) / 2 ^ w = 0 := Nat.div_eq_of_lt (by omega)
        rw [hA, hB, hdA, hdB]; decide

/-- Adding 2^w to ANY BitVec (w+1) flips its MSB (bit w)! -/
theorem getLsbD_add_pow2 {w : Nat} (a : BitVec (w + 1)) :
    (a + BitVec.cons true (0#w)).getLsbD w = !(a.getLsbD w) := by
  have hcomm : a + BitVec.cons true (0#w) = BitVec.cons true (0#w) + a := BitVec.add_comm _ _
  rw [hcomm, getLsbD_add_cons]
  have hzero : BitVec.cons false (0#w) = 0#(w + 1) := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [hzero, BitVec.zero_add]
  cases a.getLsbD w <;> rfl

/-- Exact MSB of andCarryMask: true iff both lower w-bit words are allOnes w! -/
theorem getLsbD_andCarryMask_msb {w : Nat} (x y : BitVec (w + 1)) :
    (andCarryMask x y).getLsbD w =
      decide (x.setWidth w = BitVec.allOnes w ∧ y.setWidth w = BitVec.allOnes w) := by
  simp only [andCarryMask, BitVec.getLsbD_xor]
  conv => lhs; arg 1; rw [← cons_eta (x &&& y)]
  rw [getLsbD_add_cons]
  have hxc : ∀ (a c : Bool), xor (xor a c) a = c := by
    intro a c; cases a <;> cases c <;> rfl
  rw [hxc]
  rw [getLsbD_eq_decide_div]
  simp only [BitVec.toNat_add, toNat_cons_eq, Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
    setWidth_and, BitVec.toNat_ofNat]
  have hlt : (x.setWidth w &&& y.setWidth w).toNat < 2 ^ w := (x.setWidth w &&& y.setWidth w).isLt
  have hAll : ∀ (u v : BitVec w),
      (u &&& v).toNat = 2 ^ w - 1 ↔ u = BitVec.allOnes w ∧ v = BitVec.allOnes w := by
    intro u v
    constructor
    · intro h
      have huv : u &&& v = BitVec.allOnes w := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_allOnes, h]
      constructor <;> (ext i hi; have := congrArg (fun z => z.getLsbD i) huv; simp [hi] at this; simp [this])
    · rintro ⟨rfl, rfl⟩
      simp
  have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  have hpos : 0 < 2 ^ w := Nat.pow_pos (by omega)
  have h1mod : 1 % 2 ^ (w + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1mod]
  by_cases hmax : (x.setWidth w &&& y.setWidth w).toNat = 2 ^ w - 1
  · have heq : (x.setWidth w &&& y.setWidth w).toNat + 1 = 2 ^ w := by omega
    rw [heq, Nat.mod_eq_of_lt (by omega : 2 ^ w < 2 ^ (w + 1)), Nat.div_self hpos]
    have htrue : x.setWidth w = BitVec.allOnes w ∧ y.setWidth w = BitVec.allOnes w :=
      (hAll _ _).mp hmax
    simp [htrue]
  · have hlt2 : (x.setWidth w &&& y.setWidth w).toNat + 1 < 2 ^ w := by omega
    rw [Nat.mod_eq_of_lt (by omega : (x.setWidth w &&& y.setWidth w).toNat + 1 < 2 ^ (w + 1)),
        Nat.div_eq_of_lt hlt2]
    have hfalse : ¬ (x.setWidth w = BitVec.allOnes w ∧ y.setWidth w = BitVec.allOnes w) := by
      intro h; exact hmax ((hAll _ _).mpr h)
    simp [hfalse]

/-- andCarryMask at width w+1 depends ONLY on the lower w bits of x and y! -/
theorem andCarryMask_indep_msb {w : Nat} (a b : Bool) (x y : BitVec w) :
    andCarryMask (BitVec.cons a x) (BitVec.cons b y) =
      andCarryMask (BitVec.cons false x) (BitVec.cons false y) := by
  rw [← cons_eta (andCarryMask (BitVec.cons a x) (BitVec.cons b y)),
      ← cons_eta (andCarryMask (BitVec.cons false x) (BitVec.cons false y))]
  simp only [getLsbD_andCarryMask_msb, setWidth_andCarryMask, setWidth_cons]

/-- 2 * z at width w+1 depends ONLY on z.setWidth w! -/
theorem mul2_eq_of_setWidth_eq {w : Nat} {z₁ z₂ : BitVec (w + 1)}
    (h : z₁.setWidth w = z₂.setWidth w) :
    2#(w + 1) * z₁ = 2#(w + 1) * z₂ := by
  have hnat : z₁.toNat % 2 ^ w = z₂.toNat % 2 ^ w := by
    have := congrArg BitVec.toNat h
    simpa [BitVec.toNat_setWidth] using this
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hpow]
  cases w with
  | zero => simp
  | succ w' =>
    have h2lt : 2 < 2 * 2 ^ (w' + 1) := by
      have : 2 ^ 1 ≤ 2 ^ (w' + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    rw [Nat.mod_eq_of_lt h2lt, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hnat]

/-- 4 * z at width w+2 depends ONLY on z.setWidth w! -/
theorem mul4_eq_of_setWidth_eq {w : Nat} {z₁ z₂ : BitVec (w + 2)}
    (h : z₁.setWidth w = z₂.setWidth w) :
    4#(w + 2) * z₁ = 4#(w + 2) * z₂ := by
  have hnat : z₁.toNat % 2 ^ w = z₂.toNat % 2 ^ w := by
    have := congrArg BitVec.toNat h
    simpa [BitVec.toNat_setWidth] using this
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  have hpow : 2 ^ (w + 2) = 4 * 2 ^ w := by
    rw [Nat.pow_succ, Nat.pow_succ]; omega
  rw [hpow]
  cases w with
  | zero => simp
  | succ w' =>
    have h4lt : 4 < 4 * 2 ^ (w' + 1) := by
      have : 2 ^ 1 ≤ 2 ^ (w' + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    rw [Nat.mod_eq_of_lt h4lt, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hnat]

theorem setWidth_setWidth_le {w : Nat} (z : BitVec (w + 2)) :
    (z.setWidth (w + 1)).setWidth w = z.setWidth w := by
  ext i hi
  simp

theorem bv_four_eq_two_mul_two (w : Nat) : 4#w = 2#w * 2#w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [← Nat.mul_mod]

theorem family1_fiber (P : TScalar2) (Q : TFunc1) (R : TScalar2) (w : Nat)
    (s : State w) (p : Fiber) :
    fiber (family1 P Q R) w s p =
      (D4Elem.mk (fam1Lam w s) (fam1Alpha P w s) (fam1Beta Q R w s)).apply p := by
  rcases s with ⟨x0, y0⟩
  rcases p with ⟨a, b⟩
  simp only [fiber, family1, msbPair, liftState, D4Elem.apply]
  have hm := andCarryMask_indep_msb a b x0 y0
  have hP : 2#(w + 1) * P.eval (w + 1) (BitVec.cons a x0) (BitVec.cons b y0) =
      2#(w + 1) * P.eval (w + 1) (BitVec.cons false x0) (BitVec.cons false y0) := by
    apply mul2_eq_of_setWidth_eq
    simp only [P.compat, setWidth_cons]
  have hQ : 2#(w + 1) * Q.eval (w + 1) (BitVec.cons b y0) =
      2#(w + 1) * Q.eval (w + 1) (BitVec.cons false y0) := by
    apply mul2_eq_of_setWidth_eq
    simp only [Q.compat, setWidth_cons]
  have hR : 4#(w + 1) * R.eval (w + 1) (BitVec.cons a x0) (BitVec.cons b y0) =
      4#(w + 1) * R.eval (w + 1) (BitVec.cons false x0) (BitVec.cons false y0) := by
    rw [bv_four_eq_two_mul_two, BitVec.mul_assoc, BitVec.mul_assoc]
    congr 1
    apply mul2_eq_of_setWidth_eq
    simp only [R.compat, setWidth_cons]
  apply Prod.ext
  · rw [hm, hP]
    let m1 := andCarryMask (BitVec.cons false x0) (BitVec.cons false y0)
    let p2 := 2#(w + 1) * P.eval (w + 1) (BitVec.cons false x0) (BitVec.cons false y0)
    have hym : BitVec.cons b y0 &&& m1 =
        BitVec.cons (b && m1.getLsbD w) (y0 &&& m1.setWidth w) := by
      rw [← cons_eta (BitVec.cons b y0 &&& m1)]
      simp [BitVec.getLsbD_eq_getElem]
    have hym0 : BitVec.cons false y0 &&& m1 =
        BitVec.cons false (y0 &&& m1.setWidth w) := by
      rw [← cons_eta (BitVec.cons false y0 &&& m1)]
      simp
    have hlam : m1.getLsbD w = fam1Lam w (x0, y0) := by
      have := getLsbD_andCarryMask_msb (BitVec.cons false x0) (BitVec.cons false y0)
      simpa [m1, fam1Lam] using this
    have hpull : ∀ (c : Bool) (u : BitVec w) (v : BitVec (w + 1)),
        (BitVec.cons false x0 + (BitVec.cons c u + v)).getLsbD w =
        xor c ((BitVec.cons false x0 + (BitVec.cons false u + v)).getLsbD w) := by
      intro c u v
      have h1 : BitVec.cons false x0 + (BitVec.cons c u + v) =
          BitVec.cons c u + (BitVec.cons false x0 + v) := by
        rw [← BitVec.add_assoc, BitVec.add_comm (BitVec.cons false x0), BitVec.add_assoc]
      have h2 : BitVec.cons false x0 + (BitVec.cons false u + v) =
          BitVec.cons false u + (BitVec.cons false x0 + v) := by
        rw [← BitVec.add_assoc, BitVec.add_comm (BitVec.cons false x0), BitVec.add_assoc]
      rw [h1, h2, getLsbD_add_cons]
    change (BitVec.cons a x0 + (BitVec.cons b y0 &&& m1) + p2).getLsbD w =
      xor (xor a (fam1Lam w (x0, y0) && b)) (fam1Alpha P w (x0, y0))
    rw [BitVec.add_assoc, getLsbD_add_cons a x0, hym, hpull, hlam]
    have hA : fam1Alpha P w (x0, y0) =
        (BitVec.cons false x0 + (BitVec.cons false (y0 &&& m1.setWidth w) + p2)).getLsbD w := by
      simp only [fam1Alpha, BitVec.add_assoc, m1, p2, hym0]
    rw [← hA]
    cases a <;> cases b <;> cases fam1Lam w (x0, y0) <;> cases fam1Alpha P w (x0, y0) <;> rfl
  · rw [hm, hQ, hR]
    simp only [fam1Beta]
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]
    rw [getLsbD_add_cons b y0]

/-- Shear parity of Family I: fam1Lam is true at the unique state (allOnes w, allOnes w). -/
theorem fam1Lam_xorSum (w : Nat) : xorList (fam1Lam w) (allStates w) = true := by
  apply xorList_unique_true (fam1Lam w) (allStates w) (nodup_allStates w)
    (BitVec.allOnes w, BitVec.allOnes w) (mem_allStates _)
  · simp [fam1Lam]
  · intro s _ hne
    rcases s with ⟨x, y⟩
    simp only [fam1Lam, decide_eq_false_iff_not]
    rintro ⟨rfl, rfl⟩
    exact hne rfl

/-- Helper: adding 2^w to r < 2^w cancels bit w in ((z+1) ^^^ z) whenever r + 1 < 2^w. -/
theorem nat_xor_add_two_pow_cancel {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    ((2 ^ w + a) ^^^ (2 ^ w + b)) = a ^^^ b := by
  rw [← two_pow_or_eq_add ha, ← two_pow_or_eq_add hb]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hi : w = i
  · subst hi
    simp [Nat.testBit_lt_two_pow ha, Nat.testBit_lt_two_pow hb]
  · simp [hi]

/-- Helper: exact evaluation of andCarryMask on the unique surviving involution pair. -/
theorem andCarryMask_pair_surviving (w : Nat) :
    andCarryMask (BitVec.cons false (BitVec.cons true (BitVec.allOnes w)))
                 (BitVec.cons false (BitVec.allOnes (w + 1))) =
    andCarryMask (BitVec.cons false (BitVec.cons false (BitVec.allOnes w)))
                 (BitVec.cons false (BitVec.allOnes (w + 1))) +
      BitVec.cons true (0#(w + 1)) := by
  have hlo : (BitVec.cons false (BitVec.cons false (BitVec.allOnes w)) &&&
              BitVec.cons false (BitVec.allOnes (w + 1))).toNat = 2 ^ w - 1 := by
    have heq : BitVec.cons false (BitVec.cons false (BitVec.allOnes w)) &&&
               BitVec.cons false (BitVec.allOnes (w + 1)) =
               BitVec.cons false (BitVec.cons false (BitVec.allOnes w)) := by
      ext i hi; simp
    rw [heq, toNat_cons_eq, toNat_cons_eq]
    simp [BitVec.toNat_allOnes]
  have hhi : (BitVec.cons false (BitVec.cons true (BitVec.allOnes w)) &&&
              BitVec.cons false (BitVec.allOnes (w + 1))).toNat = 2 ^ (w + 1) - 1 := by
    have heq : BitVec.cons false (BitVec.cons true (BitVec.allOnes w)) &&&
               BitVec.cons false (BitVec.allOnes (w + 1)) =
               BitVec.cons false (BitVec.allOnes (w + 1)) := by
      ext i hi
      by_cases h1 : i = w + 1
      · subst h1; simp
      · by_cases h2 : i = w
        · subst i
          simp
        · have hw : i < w := by omega
          have hw1 : i < w + 1 := by omega
          simp [hw, hw1]
    rw [heq, toNat_cons_eq]
    simp [BitVec.toNat_allOnes]
  have hpow_xor : ∀ k : Nat, (2 ^ k ^^^ (2 ^ k - 1)) = 2 ^ (k + 1) - 1 := by
    intro k
    have hlt : 2 ^ k - 1 < 2 ^ k := by have := Nat.pow_pos (a := 2) (n := k) (by omega); omega
    have hdisj : (2 ^ k ^^^ (2 ^ k - 1)) = (2 ^ k ||| (2 ^ k - 1)) := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_two_pow]
      by_cases hi : k = i
      · subst hi
        simp [Nat.testBit_lt_two_pow hlt]
      · simp [hi]
    rw [hdisj, two_pow_or_eq_add hlt, Nat.pow_succ]
    have := Nat.pow_pos (a := 2) (n := k) (by omega)
    omega
  apply BitVec.eq_of_toNat_eq
  simp only [andCarryMask, BitVec.toNat_xor, BitVec.toNat_add, BitVec.toNat_ofNat, toNat_cons_eq]
  rw [hhi, hlo]
  have hp0 : 0 < 2 ^ w := Nat.pow_pos (by omega)
  have hp1 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  have hp2 : 2 ^ (w + 2) = 2 * 2 ^ (w + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have h1m : 1 % 2 ^ (w + 2) = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1m]
  have hs1 : (2 ^ (w + 1) - 1 + 1) % 2 ^ (w + 2) = 2 ^ (w + 1) := by
    rw [show 2 ^ (w + 1) - 1 + 1 = 2 ^ (w + 1) by omega, Nat.mod_eq_of_lt (by omega)]
  have hs0 : (2 ^ w - 1 + 1) % 2 ^ (w + 2) = 2 ^ w := by
    rw [show 2 ^ w - 1 + 1 = 2 ^ w by omega, Nat.mod_eq_of_lt (by omega)]
  rw [hs1, hs0, hpow_xor (w + 1), hpow_xor w]
  simp only [↓reduceIte, Nat.zero_mod, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Helper: on every non-surviving involution pair, andCarryMask is identical! -/
theorem andCarryMask_pair_cancel {w : Nat} (x' : BitVec w) (y0 : BitVec (w + 1))
    (hne : (x', y0) ≠ (BitVec.allOnes w, BitVec.allOnes (w + 1))) :
    andCarryMask (BitVec.cons false (BitVec.cons false x')) (BitVec.cons false y0) =
    andCarryMask (BitVec.cons false (BitVec.cons true x')) (BitVec.cons false y0) := by
  by_cases hy : y0.getLsbD w = false
  · have hz : BitVec.cons false (BitVec.cons false x') &&& BitVec.cons false y0 =
              BitVec.cons false (BitVec.cons true x') &&& BitVec.cons false y0 := by
      ext i hi
      by_cases h1 : i = w + 1
      · subst h1; simp
      · by_cases h2 : i = w
        · subst i
          have hy' : y0[w] = false := by rw [← BitVec.getLsbD_eq_getElem]; exact hy
          simp [hy']
        · have hw : i < w := by omega
          have hw1 : i < w + 1 := by omega
          simp [hw, hw1]
    simp only [andCarryMask, hz]
  · have hytrue : y0.getLsbD w = true := by
      cases h : y0.getLsbD w
      · exact absurd h hy
      · rfl
    have hnotall : x' &&& y0.setWidth w ≠ BitVec.allOnes w := by
      intro hall
      apply hne
      have hxall : x' = BitVec.allOnes w := by
        ext i hi
        have := congrArg (fun z => z.getLsbD i) hall
        simp [hi] at this
        simp [this]
      have hyall : y0 = BitVec.allOnes (w + 1) := by
        ext i hi
        by_cases hwi : i = w
        · subst i
          rw [← BitVec.getLsbD_eq_getElem]
          simp [hytrue]
        · have hlt : i < w := by omega
          have := congrArg (fun z => z.getLsbD i) hall
          simp [hlt] at this
          simp [this]
      exact Prod.ext hxall hyall
    let r := (x' &&& y0.setWidth w).toNat
    have hrlt : r < 2 ^ w - 1 := by
      have hle : r < 2 ^ w := (x' &&& y0.setWidth w).isLt
      have hneq : r ≠ 2 ^ w - 1 := by
        intro heq
        apply hnotall
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_allOnes]
        exact heq
      omega
    have hz_lo : (BitVec.cons false (BitVec.cons false x') &&& BitVec.cons false y0).toNat = r := by
      have heq : BitVec.cons false (BitVec.cons false x') &&& BitVec.cons false y0 =
                 BitVec.cons false (BitVec.cons false (x' &&& y0.setWidth w)) := by
        ext i hi
        by_cases h1 : i = w + 1
        · subst h1; simp
        · by_cases h2 : i = w
          · subst i; simp
          · have hw : i < w := by omega
            have hw1 : i < w + 1 := by omega
            simp [hw, hw1]
      rw [heq, toNat_cons_eq, toNat_cons_eq]; simp [r]
    have hz_hi : (BitVec.cons false (BitVec.cons true x') &&& BitVec.cons false y0).toNat = 2 ^ w + r := by
      have heq : BitVec.cons false (BitVec.cons true x') &&& BitVec.cons false y0 =
                 BitVec.cons false (BitVec.cons true (x' &&& y0.setWidth w)) := by
        ext i hi
        by_cases h1 : i = w + 1
        · subst h1; simp
        · by_cases h2 : i = w
          · subst i
            have hy' : y0[w] = true := by rw [← BitVec.getLsbD_eq_getElem]; exact hytrue
            simp [hy']
          · have hw : i < w := by omega
            have hw1 : i < w + 1 := by omega
            simp [hw, hw1]
      rw [heq, toNat_cons_eq, toNat_cons_eq]; simp [r]
    apply BitVec.eq_of_toNat_eq
    simp only [andCarryMask, BitVec.toNat_xor, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [hz_lo, hz_hi]
    have hp0 : 0 < 2 ^ w := Nat.pow_pos (by omega)
    have hp1 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
    have hp2 : 2 ^ (w + 2) = 2 * 2 ^ (w + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have h1m : 1 % 2 ^ (w + 2) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1m, Nat.mod_eq_of_lt (by omega : r + 1 < 2 ^ (w + 2)),
        Nat.mod_eq_of_lt (by omega : 2 ^ w + r + 1 < 2 ^ (w + 2))]
    rw [show 2 ^ w + r + 1 = 2 ^ w + (r + 1) by omega]
    exact (nat_xor_add_two_pow_cancel (by omega : r + 1 < 2 ^ w) (by omega : r < 2 ^ w)).symm

/-- Y-flip parity of Family I via our Pairing-Involution XOR-Parity Engine! -/
theorem fam1Beta_xorSum (Q : TFunc1) (R : TScalar2) (w : Nat) :
    xorList (fam1Beta Q R w) (allStates w) = true := by
  cases w with
  | zero =>
    simp only [allStates, allBitVecs, List.flatMap_cons, List.flatMap_nil, List.map_cons,
      List.map_nil, List.append_nil, xorList, fam1Beta]
    have hQ0 : 2#1 * Q.eval 1 (BitVec.cons false 0#0) = 0#1 := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
    have hR0 : 4#1 * R.eval 1 (BitVec.cons false 0#0) (BitVec.cons false 0#0) = 0#1 := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]
    rw [hQ0, hR0]
    decide
  | succ w' =>
    rw [xorList_allStates_x_pair w' (fam1Beta Q R (w' + 1))]
    apply xorList_unique_true _ (halfStates w') (nodup_halfStates w')
      (BitVec.allOnes w', BitVec.allOnes (w' + 1)) (mem_halfStates _)
    · -- Surviving pair: (allOnes w', allOnes (w'+1))
      simp only [fam1Beta]
      have hReq : 4#(w' + 2) * R.eval (w' + 2) (BitVec.cons false (BitVec.cons true (BitVec.allOnes w')))
            (BitVec.cons false (BitVec.allOnes (w' + 1))) =
          4#(w' + 2) * R.eval (w' + 2) (BitVec.cons false (BitVec.cons false (BitVec.allOnes w')))
            (BitVec.cons false (BitVec.allOnes (w' + 1))) := by
        apply mul4_eq_of_setWidth_eq
        rw [← setWidth_setWidth_le, ← setWidth_setWidth_le,
            R.compat, R.compat, R.compat, R.compat]
        simp
      rw [hReq, andCarryMask_pair_surviving w']
      let y1 := BitVec.cons false (BitVec.allOnes (w' + 1))
      let m0 := andCarryMask (BitVec.cons false (BitVec.cons false (BitVec.allOnes w'))) y1
      let q2 := 2#(w' + 2) * Q.eval (w' + 2) y1
      let r4 := 4#(w' + 2) * R.eval (w' + 2)
          (BitVec.cons false (BitVec.cons false (BitVec.allOnes w'))) y1
      have hreassoc :
          y1 + (m0 + BitVec.cons true (0#(w' + 1))) + q2 + r4 =
          (y1 + m0 + q2 + r4) + BitVec.cons true (0#(w' + 1)) := by
        -- Pure abelian-group reassociation of BitVec addition!
        have h1 : y1 + (m0 + BitVec.cons true (0#(w' + 1))) =
            (y1 + m0) + BitVec.cons true (0#(w' + 1)) := (BitVec.add_assoc _ _ _).symm
        rw [h1, BitVec.add_assoc (y1 + m0), BitVec.add_comm (BitVec.cons true (0#(w' + 1))) q2,
            ← BitVec.add_assoc (y1 + m0) q2, BitVec.add_assoc (y1 + m0 + q2),
            BitVec.add_comm (BitVec.cons true (0#(w' + 1))) r4, ← BitVec.add_assoc]
      change xor ((y1 + m0 + q2 + r4).getLsbD (w' + 1))
                 ((y1 + (m0 + BitVec.cons true (0#(w' + 1))) + q2 + r4).getLsbD (w' + 1)) = true
      rw [hreassoc, getLsbD_add_pow2]
      cases (y1 + m0 + q2 + r4).getLsbD (w' + 1) <;> rfl
    · -- Non-surviving pairs: exact twin cancellation!
      intro s _ hne
      rcases s with ⟨x', y0⟩
      simp only [fam1Beta]
      have hReq : 4#(w' + 2) * R.eval (w' + 2) (BitVec.cons false (BitVec.cons true x'))
            (BitVec.cons false y0) =
          4#(w' + 2) * R.eval (w' + 2) (BitVec.cons false (BitVec.cons false x'))
            (BitVec.cons false y0) := by
        apply mul4_eq_of_setWidth_eq
        rw [← setWidth_setWidth_le, ← setWidth_setWidth_le,
            R.compat, R.compat, R.compat, R.compat]
        simp
      rw [hReq, ← andCarryMask_pair_cancel x' y0 hne]
      cases (BitVec.cons false y0 +
        andCarryMask (BitVec.cons false (BitVec.cons false x')) (BitVec.cons false y0) +
        2#(w' + 2) * Q.eval (w' + 2) (BitVec.cons false y0) +
        4#(w' + 2) * R.eval (w' + 2) (BitVec.cons false (BitVec.cons false x'))
          (BitVec.cons false y0)).getLsbD (w' + 1) <;> rfl

/--
  INFINITE THEOREM FAMILY I (UNIVERSAL NONLINEAR FULL-PERIOD 2^(2w)):
  For ANY 2-variable T-functions P, R and ANY 1-variable T-function Q,
  the coupled arithmetic-bitwise map
    T_{P,Q,R}(x, y) = (x + (y &&& m) + 2*P(x, y),  y + m + 2*Q(y) + 4*R(x, y))
  (where m = ((x &&& y) + 1) ^^^ (x &&& y)) has a SINGLE FULL CYCLE of EXACT
  minimal period 4^w = 2^(2w) on BitVec w × BitVec w for EVERY width w >= 0!
-/
theorem family1_full_period (P : TScalar2) (Q : TFunc1) (R : TScalar2) :
    ∀ w (s : State w), IsExactPeriod ((family1 P Q R).eval w) s (4 ^ w) :=
  full_period_of_D4_parity (family1 P Q R) fam1Lam (fam1Alpha P) (fam1Beta Q R)
    (family1_fiber P Q R) fam1Lam_xorSum (fam1Beta_xorSum Q R)

theorem family1_bijective (P : TScalar2) (Q : TFunc1) (R : TScalar2) (w : Nat) :
    (∀ a b, (family1 P Q R).eval w a = (family1 P Q R).eval w b → a = b) ∧
    (∀ y, ∃ x, (family1 P Q R).eval w x = y) :=
  bijective_of_full_period (family1_full_period P Q R w (0#w, 0#w))

-- ----------------------------------------------------------------------------
-- Non-Vacuity Witness & Kernel-Checked Sharpness Counterexamples for Family I
-- ----------------------------------------------------------------------------

theorem family1_nonlinear_witness_full_period :
    ∀ w (s : State w), IsExactPeriod ((family1 witnessP witnessQ witnessR).eval w) s (4 ^ w) :=
  family1_full_period witnessP witnessQ witnessR

theorem fam1Sharp2And_breaks_at_w2 :
    iter (fam1Sharp2And 2) 4 (0#2, 0#2) = (0#2, 0#2) ∧
    ¬ IsExactPeriod (fam1Sharp2And 2) (0#2, 0#2) (4 ^ 2) := by
  have h4 : iter (fam1Sharp2And 2) 4 (0#2, 0#2) = (0#2, 0#2) := by decide
  exact ⟨h4, fun hp => hp.2.2 4 (by omega) (by decide) h4⟩

theorem fam1Sharp2Mul_breaks_at_w2 :
    iter (fam1Sharp2Mul 2) 8 (0#2, 0#2) = (0#2, 0#2) ∧
    ¬ IsExactPeriod (fam1Sharp2Mul 2) (0#2, 0#2) (4 ^ 2) := by
  have h8 : iter (fam1Sharp2Mul 2) 8 (0#2, 0#2) = (0#2, 0#2) := by decide
  exact ⟨h8, fun hp => hp.2.2 8 (by omega) (by decide) h8⟩

theorem fam1NoShear_period_collapse (P : TScalar2) (Q : TFunc1) (R : TScalar2) :
    ∀ w (s : State w), iter ((fam1NoShear P Q R).eval w) (2 ^ w) s = s := by
  apply no_shear_period_bound
  intro w ⟨x0, y0⟩
  let x1 := BitVec.cons false x0
  let y1 := BitVec.cons false y0
  refine ⟨(x1 + 1#(w + 1) + 2#(w + 1) * P.eval (w + 1) x1 y1).getLsbD w,
          fam1Beta Q R w (x0, y0), ?_⟩
  rintro ⟨a, b⟩
  simp only [fiber, fam1NoShear, msbPair, liftState]
  have hm := andCarryMask_indep_msb a b x0 y0
  have hP : 2#(w + 1) * P.eval (w + 1) (BitVec.cons a x0) (BitVec.cons b y0) =
      2#(w + 1) * P.eval (w + 1) x1 y1 := by
    apply mul2_eq_of_setWidth_eq; simp [x1, y1, P.compat]
  have hQ : 2#(w + 1) * Q.eval (w + 1) (BitVec.cons b y0) =
      2#(w + 1) * Q.eval (w + 1) y1 := by
    apply mul2_eq_of_setWidth_eq; simp [y1, Q.compat]
  have hR : 4#(w + 1) * R.eval (w + 1) (BitVec.cons a x0) (BitVec.cons b y0) =
      4#(w + 1) * R.eval (w + 1) x1 y1 := by
    rw [bv_four_eq_two_mul_two, BitVec.mul_assoc, BitVec.mul_assoc]
    congr 1; apply mul2_eq_of_setWidth_eq; simp [x1, y1, R.compat]
  apply Prod.ext
  · rw [hP]
    change (BitVec.cons a x0 + 1#(w + 1) + 2#(w + 1) * P.eval (w + 1) x1 y1).getLsbD w =
      xor a ((x1 + 1#(w + 1) + 2#(w + 1) * P.eval (w + 1) x1 y1).getLsbD w)
    rw [BitVec.add_assoc (BitVec.cons a x0), BitVec.add_assoc x1, getLsbD_add_cons a x0]
  · rw [hm, hQ, hR]
    simp only [fam1Beta]
    rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]
    rw [getLsbD_add_cons b y0]

-- ============================================================================
-- PART 3: INFINITE THEOREM FAMILY II — TWISTED SILICON TERNARY ODOMETER (S4 \ D4)
-- ============================================================================

/-- Exact MSB of zeroMask y = y ^^^ (y - 1): true iff y.setWidth w = 0#w! -/
theorem getLsbD_zeroMask_msb {w : Nat} (y : BitVec (w + 1)) :
    (zeroMask y).getLsbD w = decide (y.setWidth w = 0#w) := by
  rw [← cons_eta y]
  generalize y.getLsbD w = b
  generalize y.setWidth w = y0
  have hbit_eq : ∀ u : BitVec (w + 1), (u ^^^ (u - 1#(w + 1))).getLsbD w =
      xor (u.getLsbD w) ((u - 1#(w + 1)).getLsbD w) := by
    intro u; simp
  simp only [zeroMask, hbit_eq, getLsbD_cons_self, setWidth_cons]
  have hsub_nat : (BitVec.cons b y0 - 1#(w + 1)).toNat =
      (2 ^ (w + 1) - 1 + (BitVec.cons b y0).toNat) % 2 ^ (w + 1) := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have hpos : 0 < 2 ^ w := Nat.pow_pos (by omega)
    have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [Nat.mod_eq_of_lt (by omega : 1 < 2 ^ (w + 1))]
  rw [getLsbD_eq_decide_div, hsub_nat, toNat_cons_eq]
  have hy0lt : y0.toNat < 2 ^ w := y0.isLt
  have hpos : 0 < 2 ^ w := Nat.pow_pos (by omega)
  have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  by_cases hz : y0 = 0#w
  · subst hz
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero, decide_true]
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Bool.false_xor]
      rw [Nat.mod_eq_of_lt (by omega : 2 ^ (w + 1) - 1 < 2 ^ (w + 1))]
      have hdiv : (2 ^ (w + 1) - 1) / 2 ^ w = 1 := by
        have : 2 ^ (w + 1) - 1 = 2 ^ w + (2 ^ w - 1) := by omega
        rw [this, Nat.add_div_left _ hpos, Nat.div_eq_of_lt (by omega)]
      rw [hdiv]; rfl
    | true =>
      simp only [↓reduceIte, Bool.true_xor]
      have hmod : (2 ^ (w + 1) - 1 + 2 ^ w) % 2 ^ (w + 1) = 2 ^ w - 1 := by
        have : 2 ^ (w + 1) - 1 + 2 ^ w = 2 ^ (w + 1) + (2 ^ w - 1) := by omega
        rw [this, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
            Nat.mod_eq_of_lt (by omega : 2 ^ w - 1 < 2 ^ (w + 1))]
      rw [hmod, Nat.div_eq_of_lt (by omega : 2 ^ w - 1 < 2 ^ w)]
      rfl
  · have hy0pos : 0 < y0.toNat :=
      Nat.pos_of_ne_zero (fun h0 => hz (BitVec.eq_of_toNat_eq (by simp [h0])))
    simp only [hz, decide_false]
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Bool.false_xor]
      have hmod : (2 ^ (w + 1) - 1 + y0.toNat) % 2 ^ (w + 1) = y0.toNat - 1 := by
        have : 2 ^ (w + 1) - 1 + y0.toNat = 2 ^ (w + 1) + (y0.toNat - 1) := by omega
        rw [this, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
            Nat.mod_eq_of_lt (by omega : y0.toNat - 1 < 2 ^ (w + 1))]
      rw [hmod, Nat.div_eq_of_lt (by omega : y0.toNat - 1 < 2 ^ w)]
      rfl
    | true =>
      simp only [↓reduceIte, Bool.true_xor]
      have hmod : (2 ^ (w + 1) - 1 + (2 ^ w + y0.toNat)) % 2 ^ (w + 1) = 2 ^ w + (y0.toNat - 1) := by
        have : 2 ^ (w + 1) - 1 + (2 ^ w + y0.toNat) = 2 ^ (w + 1) + (2 ^ w + (y0.toNat - 1)) := by omega
        rw [this, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
            Nat.mod_eq_of_lt (by omega : 2 ^ w + (y0.toNat - 1) < 2 ^ (w + 1))]
      rw [hmod, Nat.add_div_left _ hpos, Nat.div_eq_of_lt (by omega : y0.toNat - 1 < 2 ^ w)]
      rfl

theorem getLsbD_shiftXorY_msb {w : Nat} (shifts : List Nat) (hShifts : ∀ d ∈ shifts, 1 ≤ d)
    (b : Bool) (y0 : BitVec w) :
    (shiftXorY shifts (BitVec.cons b y0)).getLsbD w =
      xorList (fun d => if d ≤ w then y0.getLsbD (w - d) else false) shifts := by
  induction shifts with
  | nil => simp [shiftXorY, xorList]
  | cons d ds ih =>
    have hd : 1 ≤ d := hShifts d (by simp)
    have hds : ∀ d' ∈ ds, 1 ≤ d' := fun d' hd' => hShifts d' (by simp [hd'])
    simp only [shiftXorY, BitVec.getLsbD_xor, xorList, ih hds]
    congr 1
    rw [BitVec.getLsbD_shiftLeft]
    by_cases hdw : d ≤ w
    · have hlt : w - d < w := by omega
      have hnotlt : ¬ (w < d) := by omega
      simp only [hdw, ↓reduceIte, hnotlt, decide_false, Bool.not_false, Bool.true_and,
        show w < w + 1 by omega, decide_true]
      rw [BitVec.getLsbD_cons]
      have hne : ¬ (w - d = w) := by omega
      simp [hne]
    · have hlt : w < d := by omega
      simp [hdw, hlt]

theorem rot3_fix_00 : rot3 (false, false) = (false, false) := rfl

theorem rot3_period_nonzero : ∀ p : Fiber, p ≠ (false, false) → IsExactPeriod rot3 p 3 := by
  rintro ⟨a, b⟩ hne
  refine ⟨by omega, ?_, ?_⟩
  · cases a <;> cases b <;> rfl
  · intro k hk1 hk3
    have : k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl
    · cases a <;> cases b
      · exact absurd rfl hne
      · decide
      · decide
      · decide
    · cases a <;> cases b
      · exact absurd rfl hne
      · decide
      · decide
      · decide

theorem shiftBit_zero (shifts : List Nat) (w : Nat) :
    shiftBit shifts w (0#w) = false := by
  apply xorList_all_false
  intro d _
  by_cases h : d ≤ w
  · simp [h]
  · simp [h]

/-- Exact fiber of ternPoly shifts at state (x0, y0):
    - If y0 = 0#w: pure order-3 rotation rot3 ∈ S4 \ D4!
    - If y0 ≠ 0#w: pure x-bit translation (a ⊕ shiftBit shifts w y0, b)! -/
theorem ternPoly_fiber (shifts : List Nat) (hShifts : ∀ d ∈ shifts, 1 ≤ d)
    (w : Nat) (x0 y0 : BitVec w) (p : Fiber) :
    fiber (ternPoly shifts) w (x0, y0) p =
      if y0 = 0#w then rot3 p
      else (xor p.1 (shiftBit shifts w y0), p.2) := by
  rcases p with ⟨a, b⟩
  simp only [fiber, ternPoly, msbPair, liftState, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    getLsbD_cons_self, getLsbD_zeroMask_msb, setWidth_cons,
    getLsbD_shiftXorY_msb shifts hShifts b y0]
  change (xor (xor a (xor a b && decide (y0 = 0#w))) (shiftBit shifts w y0),
          xor b (a && decide (y0 = 0#w))) =
    if y0 = 0#w then rot3 (a, b) else (xor a (shiftBit shifts w y0), b)
  by_cases hy : y0 = 0#w
  · subst hy
    rw [shiftBit_zero]
    simp only [↓reduceIte, decide_true, rot3]
    cases a <;> cases b <;> rfl
  · simp only [hy, ↓reduceIte, decide_false]
    cases a <;> cases b <;> cases shiftBit shifts w y0 <;> rfl

theorem popcount_cons {w : Nat} (b : Bool) (x : BitVec w) :
    popcount (BitVec.cons b x) = (if b then 1 else 0) + popcount x := by
  simp [popcount]

/-- Helper: XOR-sum of shiftBit over an orbit list distributes over shifts. -/
theorem xorList_shiftBit_eq (shifts : List Nat) (w : Nat) (l : List (State w))
    (hEven : ∀ j < w, xorList (fun s => s.2.getLsbD j) l = false)
    (hShifts : ∀ d ∈ shifts, 1 ≤ d) :
    xorList (fun s => shiftBit shifts w s.2) l = false := by
  induction shifts with
  | nil =>
    apply xorList_all_false; intro _ _; rfl
  | cons d ds ih =>
    have hd : 1 ≤ d := hShifts d (by simp)
    have hds : ∀ d' ∈ ds, 1 ≤ d' := fun d' hd' => hShifts d' (by simp [hd'])
    have hstep : (fun s : State w => shiftBit (d :: ds) w s.2) =
        fun s => xor (if d ≤ w then s.2.getLsbD (w - d) else false) (shiftBit ds w s.2) := by
      funext s; rfl
    rw [hstep, xorList_xor, ih hds]
    by_cases hdw : d ≤ w
    · simp only [hdw, ↓reduceIte]
      rw [hEven (w - d) (by omega)]; rfl
    · simp only [hdw, ↓reduceIte]
      rw [xorList_all_false _ l (fun _ _ => rfl)]; rfl

/-- Helper: running monodromy of ternPoly shifts along an orbit starting at (x0, 0#w)
    that never revisits y = 0 for 0 < t < L. -/
theorem ternPoly_monodromy_steps (shifts : List Nat) (hShifts : ∀ d ∈ shifts, 1 ≤ d)
    (w : Nat) (x0 : BitVec w) (L : Nat)
    (hTrans : ∀ t, 0 < t → t < L → (iter ((ternPoly shifts).eval w) t (x0, 0#w)).2 ≠ 0#w) :
    ∀ k, 1 ≤ k → k ≤ L → ∀ p : Fiber,
      monodromy (ternPoly shifts) w (x0, 0#w) k p =
        (xor (rot3 p).1 (xorList (fun s => shiftBit shifts w s.2)
                          (orbitList ((ternPoly shifts).eval w) (x0, 0#w) k)),
         (rot3 p).2) := by
  intro k hk1 hkL
  induction k with
  | zero => omega
  | succ m ih =>
    intro p
    cases m with
    | zero =>
      simp only [monodromy, iter, orbitList, List.nil_append, xorList]
      rw [ternPoly_fiber shifts hShifts w x0 (0#w) p]
      simp only [↓reduceIte, shiftBit_zero]
      rcases p with ⟨a, b⟩
      cases a <;> cases b <;> rfl
    | succ m' =>
      have hm1 : 1 ≤ m' + 1 := by omega
      have hmL : m' + 1 < L := by omega
      have hne : (iter ((ternPoly shifts).eval w) (m' + 1) (x0, 0#w)).2 ≠ 0#w :=
        hTrans (m' + 1) (by omega) hmL
      change fiber (ternPoly shifts) w (iter ((ternPoly shifts).eval w) (m' + 1) (x0, 0#w))
          (monodromy (ternPoly shifts) w (x0, 0#w) (m' + 1) p) = _
      rw [ih hm1 (by omega) p]
      have hst : iter ((ternPoly shifts).eval w) (m' + 1) (x0, 0#w) =
          ((iter ((ternPoly shifts).eval w) (m' + 1) (x0, 0#w)).1,
           (iter ((ternPoly shifts).eval w) (m' + 1) (x0, 0#w)).2) := rfl
      rw [hst, ternPoly_fiber shifts hShifts w _ _ _]
      simp only [hne, ↓reduceIte]
      conv => rhs; rw [orbitList, xorList_append, xorList, xorList, Bool.xor_false]
      apply Prod.ext
      · cases (rot3 p).1 <;>
        cases xorList (fun s => shiftBit shifts w s.2)
          (orbitList ((ternPoly shifts).eval w) (x0, 0#w) (m' + 1)) <;>
        cases shiftBit shifts w (iter ((ternPoly shifts).eval w) (m' + 1) (x0, 0#w)).2 <;> rfl
      · rfl

/-- Helper: splitting orbitList of length 3 * L into 3 blocks of length L. -/
theorem orbitList_add {α : Type} (f : α → α) (s0 : α) (a b : Nat) :
    orbitList f s0 (a + b) = orbitList f s0 a ++ orbitList f (iter f a s0) b := by
  induction b with
  | zero => simp [orbitList]
  | succ b ih =>
    rw [Nat.add_succ, orbitList, orbitList, ih, List.append_assoc, iter_add]

theorem orbitList_3mul {α : Type} (f : α → α) (s0 : α) (L : Nat) :
    orbitList f s0 (3 * L) =
      orbitList f s0 L ++ orbitList f (iter f L s0) L ++ orbitList f (iter f (2 * L) s0) L := by
  have h1 : 3 * L = 2 * L + L := by omega
  have h2 : 2 * L = L + L := by omega
  rw [h1, orbitList_add, h2, orbitList_add]

/-- Helper: mapping truncState over a lifted orbit list recovers the base orbit list. -/
theorem map_truncState_orbitList (T : TFunc2) (w : Nat) (p : Fiber) (s0 : State w) (n : Nat) :
    (orbitList (T.eval (w + 1)) (liftState p s0) n).map truncState =
      orbitList (T.eval w) s0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [orbitList, List.map_append, List.map_cons, List.map_nil, ih,
      iter_liftState, truncState_liftState]

/-- Helper: y-MSB bit along a length-L lifted orbit when y only hits 0 at t = 0. -/
theorem xorList_ymsb_block (shifts : List Nat) (hShifts : ∀ d ∈ shifts, 1 ≤ d)
    (w : Nat) (x0 : BitVec w) (L : Nat) (hLpos : 0 < L)
    (hTrans : ∀ t, 0 < t → t < L → (iter ((ternPoly shifts).eval w) t (x0, 0#w)).2 ≠ 0#w)
    (p : Fiber) :
    xorList (fun s : State (w + 1) => s.2.getLsbD w)
      (orbitList ((ternPoly shifts).eval (w + 1)) (liftState p (x0, 0#w)) L) =
    xor p.2 (if (L - 1) % 2 = 1 then (rot3 p).2 else false) := by
  -- Prove for any 1 ≤ k ≤ L by induction on k!
  have hgen : ∀ k, 1 ≤ k → k ≤ L →
      xorList (fun s : State (w + 1) => s.2.getLsbD w)
        (orbitList ((ternPoly shifts).eval (w + 1)) (liftState p (x0, 0#w)) k) =
      xor p.2 (if (k - 1) % 2 = 1 then (rot3 p).2 else false) := by
    intro k hk1 hkL
    induction k with
    | zero => omega
    | succ m ih =>
      cases m with
      | zero =>
        simp [orbitList, iter, liftState, xorList]
      | succ m' =>
        rw [orbitList, xorList_append, xorList, xorList, Bool.xor_false]
        rw [ih (by omega) (by omega)]
        rw [iter_liftState]
        have hmon := ternPoly_monodromy_steps shifts hShifts w x0 L hTrans (m' + 1) (by omega) (by omega) p
        rw [hmon]
        simp only [liftState, getLsbD_cons_self]
        by_cases hm : m' % 2 = 1
        · have hm1 : ¬ ((m' + 1) % 2 = 1) := by omega
          simp only [show m' + 1 - 1 = m' by omega, show m' + 1 + 1 - 1 = m' + 1 by omega,
            hm, hm1, ↓reduceIte]
          cases p.2 <;> cases (rot3 p).2 <;> rfl
        · have hm1 : (m' + 1) % 2 = 1 := by omega
          simp only [show m' + 1 - 1 = m' by omega, show m' + 1 + 1 - 1 = m' + 1 by omega,
            hm, hm1, ↓reduceIte]
          cases p.2 <;> cases (rot3 p).2 <;> rfl
  exact hgen L hLpos (Nat.le_refl L)

/--
  JOINT POINCARÉ TRANSVERSAL + EVEN-PARITY + EXACT-PERIOD INVARIANT
  FOR THE TWISTED SILICON TERNARY ODOMETER (ALL shifts ≥ 1, ALL widths w ≥ 0):
  1. Exact period of (x, 0#w) is 3 ^ (popcount x).
  2. Unique transversal hit: y(t) ≠ 0#w for all 0 < t < 3 ^ (popcount x).
  3. Exact F2 parity cancellation: for every bit j < w, ⨁_{t=0}^{L-1} y(t)_j = false!
-/
theorem ternPoly_invariant (shifts : List Nat) (hShifts : ∀ d ∈ shifts, 1 ≤ d) :
    ∀ w (x : BitVec w),
      let f := (ternPoly shifts).eval w
      let L := 3 ^ popcount x
      IsExactPeriod f (x, 0#w) L ∧
      (∀ t, 0 < t → t < L → (iter f t (x, 0#w)).2 ≠ 0#w) ∧
      (∀ j, j < w → xorList (fun s => s.2.getLsbD j) (orbitList f (x, 0#w) L) = false) := by
  intro w
  induction w with
  | zero =>
    intro x
    have hx : x = 0#0 := Subsingleton.elim _ _
    subst hx
    have hpop0 : 3 ^ popcount 0#0 = 1 := rfl
    dsimp only
    rw [hpop0]
    refine ⟨⟨by omega, ?_, fun k hk1 hk2 => by omega⟩, fun t ht1 ht2 => by omega,
      fun j hj => by omega⟩
    exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  | succ w ih =>
    intro x
    rw [← cons_eta x]
    generalize x.getLsbD w = a
    generalize x.setWidth w = x0
    rcases ih x0 with ⟨hBase, hTrans, hEven⟩
    let L := 3 ^ popcount x0
    have hLpos : 0 < L := hBase.1
    -- Exact S4 monodromy around the length-L cycle at (x0, 0#w) is PURE rot3!
    have hMonEq : monodromy (ternPoly shifts) w (x0, 0#w) L = rot3 := by
      funext p
      rw [ternPoly_monodromy_steps shifts hShifts w x0 L hTrans L hLpos (Nat.le_refl L) p]
      rw [xorList_shiftBit_eq shifts w _ hEven hShifts]
      rcases p with ⟨pa, pb⟩
      cases pa <;> cases pb <;> rfl
    have h0cons : (0#(w + 1)) = BitVec.cons false (0#w) := by
      apply BitVec.eq_of_toNat_eq; simp
    have hLiftEq : (BitVec.cons a x0, 0#(w + 1)) = liftState (a, false) (x0, 0#w) := by
      rw [liftState, h0cons]
    have hSplit := lift_ternary_split (ternPoly shifts) w (x0, 0#w) L (false, false) hBase
      (by rw [hMonEq]; rfl) (by rw [hMonEq]; exact rot3_period_nonzero)
    cases a with
    | false =>
      have hpop : 3 ^ popcount (BitVec.cons false x0) = L := by
        simp [popcount_cons, L]
      rw [hpop, hLiftEq]
      refine ⟨hSplit.1, ?_, ?_⟩
      · intro t ht1 ht2 hzero
        have htr := congrArg (BitVec.setWidth w) hzero
        rw [iter_liftState] at htr
        simp only [liftState, setWidth_cons, setWidth_ofNat] at htr
        exact hTrans t ht1 ht2 htr
      · intro j hj
        by_cases hjw : j < w
        · have heq : (fun s : State (w + 1) => s.2.getLsbD j) =
              (fun s : State (w + 1) => (truncState s).2.getLsbD j) := by
            funext s
            simp [truncState, hjw]
          rw [heq, ← xorList_map (fun s : State w => s.2.getLsbD j) truncState,
              map_truncState_orbitList]
          exact hEven j hjw
        · have hjw' : j = w := by omega
          subst j
          rw [xorList_ymsb_block shifts hShifts w x0 L hLpos hTrans (false, false)]
          simp [rot3]
    | true =>
      have hpop : 3 ^ popcount (BitVec.cons true x0) = 3 * L := by
        simp only [popcount_cons, ↓reduceIte, L]
        rw [Nat.add_comm, Nat.pow_succ, Nat.mul_comm]
      rw [hpop, hLiftEq]
      refine ⟨hSplit.2 (true, false) (by decide), ?_, ?_⟩
      · intro t ht1 ht2 hzero
        let q := t / L
        have hq : q < 3 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact ht2)
        have hr : t % L < L := Nat.mod_lt t hLpos
        have ht_eq : t = q * L + t % L := by
          rw [Nat.mul_comm]; exact (Nat.div_add_mod t L).symm
        by_cases hr0 : t % L = 0
        · have htq : t = q * L := by rw [ht_eq, hr0, Nat.add_zero]
          have hqne0 : q ≠ 0 := by
            intro h0; rw [h0, Nat.zero_mul] at htq; omega
          have hqpos : q = 1 ∨ q = 2 := by
            have hq0 := Nat.zero_le q
            revert hq hqne0
            cases q with
            | zero => intro _ hne; exact absurd rfl hne
            | succ q' =>
              cases q' with
              | zero => intro _ _; exact Or.inl rfl
              | succ q'' =>
                cases q'' with
                | zero => intro _ _; exact Or.inr rfl
                | succ m => intro hlt _; omega
          have hiter : iter ((ternPoly shifts).eval (w + 1)) t (liftState (true, false) (x0, 0#w)) =
              liftState (iter rot3 q (true, false)) (x0, 0#w) := by
            rw [htq, iter_liftState,
                monodromy_mul_fixed (ternPoly shifts) w (x0, 0#w) L hBase.2.1 q,
                iter_mul_fixed ((ternPoly shifts).eval w) L (x0, 0#w) hBase.2.1 q,
                hMonEq]
          rw [hiter] at hzero
          have hmsb := congrArg (fun z : BitVec (w + 1) => z.getLsbD w) hzero
          simp only [liftState, getLsbD_cons_self, BitVec.getLsbD_zero] at hmsb
          rcases hqpos with h1 | h2
          · rw [h1] at hmsb; exact absurd hmsb (by decide)
          · rw [h2] at hmsb; exact absurd hmsb (by decide)
        · have htr := congrArg (BitVec.setWidth w) hzero
          rw [iter_liftState] at htr
          simp only [liftState, setWidth_cons, setWidth_ofNat] at htr
          rw [iter_mod_fixed ((ternPoly shifts).eval w) L (x0, 0#w) hBase.2.1 t] at htr
          exact hTrans (t % L) (by omega) hr htr
      · intro j hj
        rw [orbitList_3mul, xorList_append, xorList_append]
        have h1L : iter ((ternPoly shifts).eval (w + 1)) L (liftState (true, false) (x0, 0#w)) =
            liftState (false, true) (x0, 0#w) := by
          rw [iter_liftState, hBase.2.1, hMonEq]; rfl
        have h2L : iter ((ternPoly shifts).eval (w + 1)) (2 * L) (liftState (true, false) (x0, 0#w)) =
            liftState (true, true) (x0, 0#w) := by
          rw [iter_liftState,
              monodromy_mul_fixed (ternPoly shifts) w (x0, 0#w) L hBase.2.1 2,
              iter_mul_fixed ((ternPoly shifts).eval w) L (x0, 0#w) hBase.2.1 2, hMonEq]; rfl
        rw [h1L, h2L]
        by_cases hjw : j < w
        · have heq : (fun s : State (w + 1) => s.2.getLsbD j) =
              (fun s : State (w + 1) => (truncState s).2.getLsbD j) := by
            funext s
            simp [truncState, hjw]
          rw [heq,
              ← xorList_map (fun s : State w => s.2.getLsbD j) truncState,
              ← xorList_map (fun s : State w => s.2.getLsbD j) truncState,
              ← xorList_map (fun s : State w => s.2.getLsbD j) truncState,
              map_truncState_orbitList, map_truncState_orbitList, map_truncState_orbitList,
              hEven j hjw]
          rfl
        · have hjw' : j = w := by omega
          subst j
          rw [xorList_ymsb_block shifts hShifts w x0 L hLpos hTrans (true, false),
              xorList_ymsb_block shifts hShifts w x0 L hLpos hTrans (false, true),
              xorList_ymsb_block shifts hShifts w x0 L hLpos hTrans (true, true)]
          by_cases hp : (L - 1) % 2 = 1 <;> simp [hp, rot3]

/-- Exact sum identity: ∑_{x ∈ BitVec w} 3^(popcount x) = 4^w. -/
theorem sum_three_pow_popcount (w : Nat) :
    ((allBitVecs w).map (fun x => 3 ^ popcount x)).sum = 4 ^ w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp only [allBitVecs, List.map_append, List.sum_append, List.map_map]
    have h0 : (fun x : BitVec w => 3 ^ popcount (BitVec.cons false x)) =
        (fun x => 3 ^ popcount x) := by
      funext x; simp [popcount_cons]
    have h1 : (fun x : BitVec w => 3 ^ popcount (BitVec.cons true x)) =
        (fun x => 3 * 3 ^ popcount x) := by
      funext x
      simp only [popcount_cons, ↓reduceIte]
      rw [Nat.add_comm, Nat.pow_succ, Nat.mul_comm]
    have hmul : ∀ (l : List Nat) (c : Nat), (l.map (fun n => c * n)).sum = c * l.sum := by
      intro l c
      induction l with
      | nil => simp
      | cons a t iht => simp [iht, Nat.mul_add]
    have hcomp0 : (fun x => 3 ^ popcount x) ∘ BitVec.cons false = fun x => 3 ^ popcount x := h0
    have hcomp1 : (fun x => 3 ^ popcount x) ∘ BitVec.cons true = fun x => 3 * 3 ^ popcount x := h1
    have hmap : (allBitVecs w).map (fun x => 3 * 3 ^ popcount x) =
        ((allBitVecs w).map (fun x => 3 ^ popcount x)).map (fun n => 3 * n) := by
      simp [List.map_map]
    rw [hcomp0, hcomp1, hmap, hmul, ih, Nat.pow_succ]
    omega

/-- Exact binomial weight count: #{x ∈ BitVec w | popcount x = k} = choose w k! -/
theorem countP_popcount_eq_choose (w k : Nat) :
    (allBitVecs w).countP (fun x => decide (popcount x = k)) = choose w k := by
  induction w generalizing k with
  | zero =>
    cases k with
    | zero => rfl
    | succ k' => rfl
  | succ w ih =>
    simp only [allBitVecs, List.countP_append, List.countP_map]
    have h0 : ((fun x : BitVec (w + 1) => decide (popcount x = k)) ∘ BitVec.cons false) =
        (fun x : BitVec w => decide (popcount x = k)) := by
      funext x; simp [popcount_cons]
    rw [h0, ih k]
    cases k with
    | zero =>
      have h1 : ((fun x : BitVec (w + 1) => decide (popcount x = 0)) ∘ BitVec.cons true) =
          (fun _ : BitVec w => false) := by
        funext x; simp [popcount_cons]
      have hzero : ∀ (l : List (BitVec w)), l.countP (fun _ => false) = 0 := by
        intro l; induction l with | nil => rfl | cons _ t iht => simp [iht]
      rw [h1, hzero]
      simp [choose]
    | succ k' =>
      have h1 : ((fun x : BitVec (w + 1) => decide (popcount x = k' + 1)) ∘ BitVec.cons true) =
          (fun x : BitVec w => decide (popcount x = k')) := by
        funext x; simp [popcount_cons, Nat.add_comm]
      rw [h1, ih k']
      simp [choose, Nat.add_comm]

/--
  INFINITE THEOREM FAMILY II (EXACT BINOMIAL CYCLE PARTITION OF TWISTED TERNARY ODOMETER):
  For ANY strictly-positive shift list `shifts` (∀ d ∈ shifts, d ≥ 1) and EVERY width w ≥ 0:
  1. The 2^w orbits starting at the Poincaré transversal {(x, 0#w) | x ∈ BitVec w}
     have exact minimal periods 3^(popcount x), are pairwise disjoint, and their
     concatenation is an EXACT permutation of all 4^w states of BitVec w × BitVec w!
  2. For every k ≤ w, there are EXACTLY `choose w k` cycles of length 3^k (total 2^w
     cycles, maximum period 3^w).
  3. Every state s ∈ BitVec w × BitVec w belongs to a UNIQUE transversal cycle!
-/
theorem ternPoly_exact_cycle_partition (shifts : List Nat) (hShifts : ∀ d ∈ shifts, 1 ≤ d)
    (w : Nat) :
    let f := (ternPoly shifts).eval w
    ((allBitVecs w).flatMap (fun x => orbitList f (x, 0#w) (3 ^ popcount x))).Perm (allStates w) ∧
    (∀ x : BitVec w, IsExactPeriod f (x, 0#w) (3 ^ popcount x)) ∧
    (∀ k : Nat, (allBitVecs w).countP (fun x => decide (popcount x = k)) = choose w k) := by
  let f := (ternPoly shifts).eval w
  have hInv := ternPoly_invariant shifts hShifts w
  refine ⟨?_, fun x => (hInv x).1, fun k => countP_popcount_eq_choose w k⟩
  apply perm_of_nodup_subset_len _ (nodup_allStates w)
  · rw [List.length_flatMap, allStates_length]
    have hlen : (allBitVecs w).map (fun x => (orbitList f (x, 0#w) (3 ^ popcount x)).length) =
        (allBitVecs w).map (fun x => 3 ^ popcount x) := by
      congr 1; funext x; exact orbitList_length _ _ _
    rw [hlen, sum_three_pow_popcount]
  · intro s _; exact mem_allStates s
  · apply nodup_flatMap_aux (nodup_allBitVecs w)
    · intro x _
      exact nodup_orbitList (hInv x).1 _ (Nat.le_refl _)
    · intro x₁ _ x₂ _ hne s h1 h2
      rw [mem_orbitList_iff] at h1 h2
      rcases h1 with ⟨k₁, hk₁, rfl⟩
      rcases h2 with ⟨k₂, hk₂, heq⟩
      -- iter f k₂ (x₂, 0#w) = iter f k₁ (x₁, 0#w), so applying f^(L₁ - k₁) gives (x₁, 0#w)!
      have hL₁ := (hInv x₁).1.2.1
      have hL₂ := (hInv x₂).1.2.1
      have hhit : iter f (k₂ + (3 ^ popcount x₁ - k₁)) (x₂, 0#w) = (x₁, 0#w) := by
        rw [iter_add, heq, ← iter_add, show k₁ + (3 ^ popcount x₁ - k₁) = 3 ^ popcount x₁ by omega, hL₁]
      rw [iter_mod_fixed f (3 ^ popcount x₂) (x₂, 0#w) hL₂] at hhit
      have hmodlt : (k₂ + (3 ^ popcount x₁ - k₁)) % 3 ^ popcount x₂ < 3 ^ popcount x₂ :=
        Nat.mod_lt _ (hInv x₂).1.1
      by_cases hm0 : (k₂ + (3 ^ popcount x₁ - k₁)) % 3 ^ popcount x₂ = 0
      · rw [hm0, iter_zero] at hhit
        exact hne (Prod.mk.inj hhit).1.symm
      · have hy0 : (iter f ((k₂ + (3 ^ popcount x₁ - k₁)) % 3 ^ popcount x₂) (x₂, 0#w)).2 = 0#w := by
          rw [hhit]
        exact (hInv x₂).2.1 _ (by omega) hmodlt hy0

-- Non-vacuity witness for Family II: Twisted Ternary + XOR(2*y) (shifts = [1])
-- Explicitly destroys the naive bitwise-OR invariant (x ||| y)!

theorem ternTwistY_exact_partition (w : Nat) :
    ((allBitVecs w).flatMap (fun x => orbitList ((ternPoly [1]).eval w) (x, 0#w) (3 ^ popcount x))).Perm
      (allStates w) ∧
    (∀ x : BitVec w, IsExactPeriod ((ternPoly [1]).eval w) (x, 0#w) (3 ^ popcount x)) := by
  have h := ternPoly_exact_cycle_partition [1] (fun d hd => by simp at hd; omega) w
  exact ⟨h.1, h.2.1⟩

/-- Non-triviality witness: Ternary + XOR(2*y) genuinely breaks (x ||| y) invariance! -/
theorem ternTwistY_destroys_or_invariant :
    let s' := (ternPoly [1]).eval 2 (0#2, 1#2)
    (s'.1 ||| s'.2) ≠ (0#2 ||| 1#2) := by
  decide

theorem ternSharpX_breaks_at_w5 :
    IsExactPeriod (ternSharpX 5) (0#5, 9#5) 18 := by
  refine ⟨by omega, by decide, ?_⟩
  intro k hk1 hk18
  have hcases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
      k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

-- ============================================================================
-- PART 4: INFINITE THEOREM FAMILY III — HYBRID S4 TWO-CYCLE MAP {4^(w-1), 3*4^(w-1)}
-- ============================================================================

theorem hybridTrig_bit0 (c : Bool) (w : Nat) :
    ((hybridTrig c w).1.getLsbD 0, (hybridTrig c w).2.getLsbD 0) = (c, false) := by
  induction w with
  | zero => simp [hybridTrig]
  | succ k ih =>
    simp only [hybridTrig, liftState, BitVec.getLsbD_cons, Nat.zero_ne_add_one, ↓reduceIte]
    exact ih

theorem hybridZ_eq_allOnes_iff {w : Nat} (x y : BitVec (w + 1)) :
    hybridZ x y = BitVec.allOnes (w + 1) ↔ (x, y) = hybridTrig (x.getLsbD 0) w := by
  have htrig : ∀ (c : Bool) (k : Nat) (i : Nat) (hi : i < k + 1),
      (hybridTrig c k).1.getLsbD i = (if i = 0 then c else true) ∧
      (hybridTrig c k).2.getLsbD i = (if i = 0 then false else true) := by
    intro c k
    induction k with
    | zero =>
      intro i hi
      have : i = 0 := by omega
      subst this
      simp [hybridTrig]
    | succ k ih =>
      intro i hi
      by_cases htop : i = k + 1
      · subst htop
        simp [hybridTrig, liftState]
      · have hlt : i < k + 1 := by omega
        have := ih i hlt
        simp only [hybridTrig, liftState, BitVec.getLsbD_cons, htop, ↓reduceIte]
        exact this
  constructor
  · intro hall
    apply Prod.ext <;> (
      ext i hi
      have hbit := congrArg (fun z : BitVec (w + 1) => z.getLsbD i) hall
      simp only [hybridZ, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
        BitVec.getLsbD_xor, BitVec.getLsbD_allOnes, hi, decide_true] at hbit
      have ht := htrig (x.getLsbD 0) w i hi
      rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
      by_cases hi0 : i = 0
      · subst hi0
        simp only [ht.1, ht.2, ↓reduceIte]
        try (
          have h10 : (1#(w + 1)).getLsbD 0 = true := by simp
          simp only [h10, Bool.not_true, Bool.and_false, Bool.false_or, Bool.and_true] at hbit
          cases h : y.getLsbD 0 <;> simp_all)
      · have h1i : (1#(w + 1)).getLsbD i = false := by simp [hi0]
        simp only [hi0, ↓reduceIte, ht.1, ht.2]
        simp only [h1i, Bool.not_false, Bool.and_true, Bool.and_false, Bool.or_false] at hbit
        cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all)
  · intro heq
    have hx : x = (hybridTrig (x.getLsbD 0) w).1 := congrArg Prod.fst heq
    have hy : y = (hybridTrig (x.getLsbD 0) w).2 := congrArg Prod.snd heq
    ext i hi
    rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
    simp only [hybridZ, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_xor, BitVec.getLsbD_allOnes, hi, decide_true]
    have ht := htrig (x.getLsbD 0) w i hi
    rw [hx, hy, ht.1, ht.2]
    by_cases hi0 : i = 0
    · subst hi0; simp
    · have h1i : (1#(w + 1)).getLsbD i = false := by simp [hi0]
      simp [hi0, h1i]

theorem hybridTwoCycle_fiber (w : Nat) (s : State (w + 1)) (p : Fiber) :
    fiber hybridTwoCycle (w + 1) s p =
      (D4Elem.mk (decide (hybridZ s.1 s.2 = BitVec.allOnes (w + 1)))
                 false
                 (decide (hybridZ s.1 s.2 = BitVec.allOnes (w + 1)))).apply p := by
  rcases s with ⟨x0, y0⟩
  rcases p with ⟨a, b⟩
  simp only [fiber, hybridTwoCycle, msbPair, liftState, D4Elem.apply]
  have h1hi : (1#(w + 2)).getLsbD (w + 1) = false := by simp
  have hmbit : (hybridMaskHi (BitVec.cons a x0) (BitVec.cons b y0)).getLsbD (w + 1) =
      decide (hybridZ x0 y0 = BitVec.allOnes (w + 1)) := by
    simp only [hybridMaskHi, BitVec.getLsbD_and, BitVec.getLsbD_not, h1hi, Bool.not_false,
      Bool.and_true, show w + 1 < w + 2 by omega, decide_true]
    let z := hybridZ (BitVec.cons a x0) (BitVec.cons b y0)
    have hzw : z.setWidth (w + 1) = hybridZ x0 y0 := by
      have hnot1 : (~~~(1#(w + 2))).setWidth (w + 1) = ~~~(1#(w + 1)) := by
        ext i hi; simp
      have hor : ∀ u v : BitVec (w + 2),
          (u ||| v).setWidth (w + 1) = u.setWidth (w + 1) ||| v.setWidth (w + 1) := by
        intro u v; ext i hi; simp
      simp only [z, hybridZ, hor, setWidth_and, setWidth_xor, hnot1, setWidth_ofNat, setWidth_cons]
    have hcm := getLsbD_andCarryMask_msb z z
    have hzz : z &&& z = z := by ext i hi; simp
    simp only [andCarryMask, hzz] at hcm
    rw [hcm, hzw]
    by_cases h : hybridZ x0 y0 = BitVec.allOnes (w + 1) <;> simp [h]
  apply Prod.ext
  · simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
      h1hi, Bool.not_false, Bool.and_true, Bool.and_false, Bool.or_false,
      getLsbD_cons_self, hmbit, show w + 1 < w + 2 by omega, decide_true]
    cases a <;> cases b <;> cases decide (hybridZ x0 y0 = BitVec.allOnes (w + 1)) <;> rfl
  · simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
      h1hi, Bool.not_false, Bool.and_true, Bool.and_false, Bool.or_false,
      getLsbD_cons_self, hmbit, show w + 1 < w + 2 by omega, decide_true]

theorem hybridTwoCycle_bit0 (w : Nat) (s : State (w + 1)) :
    let s' := hybridTwoCycle.eval (w + 1) s
    (s'.1.getLsbD 0, s'.2.getLsbD 0) = rot3 (s.1.getLsbD 0, s.2.getLsbD 0) := by
  rcases s with ⟨x, y⟩
  have h10 : (1#(w + 1)).getLsbD 0 = true := by simp
  simp only [hybridTwoCycle, rot3, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_xor, h10, Bool.not_true, Bool.and_false, Bool.false_or, Bool.and_true,
    Nat.zero_lt_succ, decide_true]

theorem hybridTwoCycle_iter_bit0 (w : Nat) (n : Nat) (s : State (w + 1)) :
    let sn := iter (hybridTwoCycle.eval (w + 1)) n s
    (sn.1.getLsbD 0, sn.2.getLsbD 0) = iter rot3 n (s.1.getLsbD 0, s.2.getLsbD 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iter_succ, iter_succ, ← ih]
    exact hybridTwoCycle_bit0 w _

/--
  INFINITE THEOREM FAMILY III (HYBRID S4 TWO-CYCLE DECOMPOSITION):
  For EVERY width w >= 1 (written w' + 1):
  1. (0#(w'+1), 0#(w'+1)) has EXACT minimal period 4^w'.
  2. (1#(w'+1), 0#(w'+1)) has EXACT minimal period 3 * 4^w'.
  3. Their two disjoint orbits concatenate to an EXACT permutation of ALL 4^(w'+1) states!
-/
theorem hybridTwoCycle_exact_two_cycles (w' : Nat) :
    let f := hybridTwoCycle.eval (w' + 1)
    IsExactPeriod f (0#(w' + 1), 0#(w' + 1)) (4 ^ w') ∧
    IsExactPeriod f (1#(w' + 1), 0#(w' + 1)) (3 * 4 ^ w') ∧
    (orbitList f (0#(w' + 1), 0#(w' + 1)) (4 ^ w') ++
     orbitList f (1#(w' + 1), 0#(w' + 1)) (3 * 4 ^ w')).Perm (allStates (w' + 1)) := by
  induction w' with
  | zero =>
    have hp0 : IsExactPeriod (hybridTwoCycle.eval 1) (0#1, 0#1) 1 :=
      ⟨by omega, by decide, fun k hk1 hk2 => by omega⟩
    have hp1 : IsExactPeriod (hybridTwoCycle.eval 1) (1#1, 0#1) 3 := by
      refine ⟨by omega, by decide, ?_⟩
      intro k hk1 hk3
      have : k = 1 ∨ k = 2 := by omega
      rcases this with rfl | rfl <;> decide
    refine ⟨hp0, hp1, ?_⟩
    apply perm_of_nodup_subset_len _ (nodup_allStates 1)
    · simp [orbitList_length, allStates_length]
    · intro x _; exact mem_allStates x
    · decide
  | succ w ih =>
    rcases ih with ⟨hP0, hP1, hPerm⟩
    let f := hybridTwoCycle.eval (w + 1)
    let lam : State (w + 1) → Bool := fun s => decide (hybridZ s.1 s.2 = BitVec.allOnes (w + 1))
    have horb0_bit0 : ∀ s ∈ orbitList f (0#(w + 1), 0#(w + 1)) (4 ^ w),
        (s.1.getLsbD 0, s.2.getLsbD 0) = (false, false) := by
      intro s hs
      rw [mem_orbitList_iff] at hs
      rcases hs with ⟨k, _, rfl⟩
      rw [hybridTwoCycle_iter_bit0]
      simp only [BitVec.getLsbD_zero]
      have hfix := iter_mul_fixed rot3 1 (false, false) rfl k
      simpa [Nat.mul_one] using hfix
    have horb1_bit0 : ∀ s ∈ orbitList f (1#(w + 1), 0#(w + 1)) (3 * 4 ^ w),
        (s.1.getLsbD 0, s.2.getLsbD 0) ≠ (false, false) := by
      intro s hs
      rw [mem_orbitList_iff] at hs
      rcases hs with ⟨k, _, rfl⟩
      rw [hybridTwoCycle_iter_bit0]
      have h10 : (1#(w + 1)).getLsbD 0 = true := by simp
      rw [h10, BitVec.getLsbD_zero]
      rw [iter_mod_fixed rot3 3 (true, false) rfl k]
      have hlt : k % 3 < 3 := Nat.mod_lt k (by omega)
      have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases this with h | h | h <;> rw [h] <;> decide
    have hT0_mem : hybridTrig false w ∈ orbitList f (0#(w + 1), 0#(w + 1)) (4 ^ w) := by
      have hall := hPerm.symm.subset (mem_allStates (hybridTrig false w))
      rw [List.mem_append] at hall
      rcases hall with h0 | h1
      · exact h0
      · exact absurd (hybridTrig_bit0 false w) (horb1_bit0 _ h1)
    have hT1_mem : hybridTrig true w ∈ orbitList f (1#(w + 1), 0#(w + 1)) (3 * 4 ^ w) := by
      have hall := hPerm.symm.subset (mem_allStates (hybridTrig true w))
      rw [List.mem_append] at hall
      rcases hall with h0 | h1
      · exfalso
        have hbit := hybridTrig_bit0 true w
        have := horb0_bit0 _ h0
        rw [hbit] at this; exact absurd this (by decide)
      · exact h1
    have hLam0 : xorList lam (orbitList f (0#(w + 1), 0#(w + 1)) (4 ^ w)) = true := by
      apply xorList_unique_true lam _ (nodup_orbitList hP0 _ (Nat.le_refl _))
        (hybridTrig false w) hT0_mem
      · simp only [lam, decide_eq_true_eq]
        rw [hybridZ_eq_allOnes_iff]
        have hbit0 : (hybridTrig false w).1.getLsbD 0 = false := (Prod.mk.inj (hybridTrig_bit0 false w)).1
        rw [hbit0]
      · intro s hs hne
        simp only [lam, decide_eq_false_iff_not]
        rw [hybridZ_eq_allOnes_iff]
        have hbit0 : s.1.getLsbD 0 = false := (Prod.mk.inj (horb0_bit0 s hs)).1
        rw [hbit0]
        exact hne
    have hLam1 : xorList lam (orbitList f (1#(w + 1), 0#(w + 1)) (3 * 4 ^ w)) = true := by
      apply xorList_unique_true lam _ (nodup_orbitList hP1 _ (Nat.le_refl _))
        (hybridTrig true w) hT1_mem
      · simp only [lam, decide_eq_true_eq]
        rw [hybridZ_eq_allOnes_iff]
        have hbit0 : (hybridTrig true w).1.getLsbD 0 = true := (Prod.mk.inj (hybridTrig_bit0 true w)).1
        rw [hbit0]
      · intro s hs hne
        simp only [lam, decide_eq_false_iff_not]
        rw [hybridZ_eq_allOnes_iff]
        intro heq
        have hbit0 : s.1.getLsbD 0 = true := by
          by_cases h0 : s.1.getLsbD 0 = true
          · exact h0
          · have hf : s.1.getLsbD 0 = false := by cases h : s.1.getLsbD 0 <;> simp_all
            rw [hf] at heq
            have hbit : (s.1.getLsbD 0, s.2.getLsbD 0) = (false, false) := by
              have h1 : s.1 = (hybridTrig false w).1 := congrArg Prod.fst heq
              have h2 : s.2 = (hybridTrig false w).2 := congrArg Prod.snd heq
              rw [h1, h2]
              exact hybridTrig_bit0 false w
            exact absurd hbit (horb1_bit0 s hs)
        rw [hbit0] at heq
        exact hne heq
    have h0lift : (0#(w + 2), 0#(w + 2)) = liftState (false, false) (0#(w + 1), 0#(w + 1)) := by
      apply Prod.ext <;> (apply BitVec.eq_of_toNat_eq; simp [liftState])
    have h1lift : (1#(w + 2), 0#(w + 2)) = liftState (false, false) (1#(w + 1), 0#(w + 1)) := by
      apply Prod.ext
      · apply BitVec.eq_of_toNat_eq
        simp only [liftState, toNat_cons_eq, Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
          BitVec.toNat_ofNat]
        have hp1 : 1 < 2 ^ (w + 1) := by
          have : 2 ^ 1 ≤ 2 ^ (w + 1) := Nat.pow_le_pow_right (by omega) (by omega); omega
        have hp2 : 1 < 2 ^ (w + 2) := by
          have : 2 ^ 1 ≤ 2 ^ (w + 2) := Nat.pow_le_pow_right (by omega) (by omega); omega
        rw [Nat.mod_eq_of_lt hp1, Nat.mod_eq_of_lt hp2]
      · apply BitVec.eq_of_toNat_eq; simp [liftState]
    have hQ0 : IsExactPeriod (hybridTwoCycle.eval (w + 2)) (0#(w + 2), 0#(w + 2)) (4 ^ (w + 1)) := by
      rw [h0lift]
      let M := d4Monodromy hybridTwoCycle (w + 1) lam (fun _ => false) lam (0#(w + 1), 0#(w + 1)) (4 ^ w)
      have hM4 : ∀ p, IsExactPeriod (monodromy hybridTwoCycle (w + 1) (0#(w + 1), 0#(w + 1)) (4 ^ w)) p 4 := by
        intro p
        have hfun : monodromy hybridTwoCycle (w + 1) (0#(w + 1), 0#(w + 1)) (4 ^ w) = M.apply :=
          funext (d4Monodromy_apply hybridTwoCycle (w + 1) lam (fun _ => false) lam
            (hybridTwoCycle_fiber w) (0#(w + 1), 0#(w + 1)) (4 ^ w))
        rw [hfun]
        exact (D4Elem.is_4cycle_iff M).mpr
          ⟨by show (d4Monodromy _ _ _ _ _ _ _).lam = true; rw [d4Monodromy_lam]; exact hLam0,
           by show (d4Monodromy _ _ _ _ _ _ _).beta = true; rw [d4Monodromy_beta]; exact hLam0⟩ p
      have h := lift_quadruple hybridTwoCycle (w + 1) (0#(w + 1), 0#(w + 1)) (4 ^ w) hP0 hM4 (false, false)
      have hpow : 4 * 4 ^ w = 4 ^ (w + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      rwa [hpow] at h
    have hQ1 : IsExactPeriod (hybridTwoCycle.eval (w + 2)) (1#(w + 2), 0#(w + 2)) (3 * 4 ^ (w + 1)) := by
      rw [h1lift]
      let M := d4Monodromy hybridTwoCycle (w + 1) lam (fun _ => false) lam (1#(w + 1), 0#(w + 1)) (3 * 4 ^ w)
      have hM4 : ∀ p, IsExactPeriod (monodromy hybridTwoCycle (w + 1) (1#(w + 1), 0#(w + 1)) (3 * 4 ^ w)) p 4 := by
        intro p
        have hfun : monodromy hybridTwoCycle (w + 1) (1#(w + 1), 0#(w + 1)) (3 * 4 ^ w) = M.apply :=
          funext (d4Monodromy_apply hybridTwoCycle (w + 1) lam (fun _ => false) lam
            (hybridTwoCycle_fiber w) (1#(w + 1), 0#(w + 1)) (3 * 4 ^ w))
        rw [hfun]
        exact (D4Elem.is_4cycle_iff M).mpr
          ⟨by show (d4Monodromy _ _ _ _ _ _ _).lam = true; rw [d4Monodromy_lam]; exact hLam1,
           by show (d4Monodromy _ _ _ _ _ _ _).beta = true; rw [d4Monodromy_beta]; exact hLam1⟩ p
      have h := lift_quadruple hybridTwoCycle (w + 1) (1#(w + 1), 0#(w + 1)) (3 * 4 ^ w) hP1 hM4 (false, false)
      have hpow : 4 * (3 * 4 ^ w) = 3 * 4 ^ (w + 1) := by rw [Nat.pow_succ]; omega
      rwa [hpow] at h
    refine ⟨hQ0, hQ1, ?_⟩
    apply perm_of_nodup_subset_len _ (nodup_allStates (w + 2))
    · simp only [List.length_append, orbitList_length, allStates_length, Nat.pow_succ]
      omega
    · intro x _; exact mem_allStates x
    · rw [List.nodup_append]
      refine ⟨nodup_orbitList hQ0 _ (Nat.le_refl _), nodup_orbitList hQ1 _ (Nat.le_refl _), ?_⟩
      intro a ha b hb heq
      subst heq
      rw [mem_orbitList_iff] at ha hb
      rcases ha with ⟨k0, _, rfl⟩
      rcases hb with ⟨k1, _, heqk⟩
      have hb0 := hybridTwoCycle_iter_bit0 (w + 1) k0 (0#(w + 2), 0#(w + 2))
      have hb1 := hybridTwoCycle_iter_bit0 (w + 1) k1 (1#(w + 2), 0#(w + 2))
      rw [heqk] at hb1
      have h00 : iter rot3 k0 ((0#(w + 2)).getLsbD 0, (0#(w + 2)).getLsbD 0) = (false, false) := by
        simp only [BitVec.getLsbD_zero]
        simpa [Nat.mul_one] using iter_mul_fixed rot3 1 (false, false) rfl k0
      have h10 : (1#(w + 2)).getLsbD 0 = true := by simp
      have hne : iter rot3 k1 (true, false) ≠ (false, false) := by
        rw [iter_mod_fixed rot3 3 (true, false) rfl k1]
        have hlt : k1 % 3 < 3 := Nat.mod_lt k1 (by omega)
        have : k1 % 3 = 0 ∨ k1 % 3 = 1 ∨ k1 % 3 = 2 := by omega
        rcases this with h | h | h <;> rw [h] <;> decide
      rw [h00] at hb0
      rw [h10, BitVec.getLsbD_zero] at hb1
      exact hne (hb1.symm.trans hb0)

end CoupledS4TFunction
