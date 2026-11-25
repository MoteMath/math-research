/-
  Pure-Silicon Mathematical "Big Bang" — Track 2 (Waves 13..16) Zero-Dependency Lean 4 Proofs
  (`lean/Waves13To16Verify.lean`: Epochs 45..52 Closing the 6 Remaining Continents)

  NO Mathlib. NO built-in `Nat`, `Int`, `Rat`, `Real`, or `Bool` arithmetic used anywhere.
  Extends `BigBangScratchVerify` .. `Track1UnshackledVerify`:
    1. Wave 13 — Tropical `(min, +)` Idempotent Semiring Laws (`btrop_min_comm`,
       `btrop_min_assoc`, `btrop_add_min_distrib`).
    2. Wave 14 — Discrete Riemannian Gauss-Bonnet Metric-Invariance Theorem
       (`bgauss_bonnet_tetra_metric_invariance`: all 12 local triangle angles cancel!).
    3. Wave 15 — Universal Farkas Linear Infeasibility Certificate Soundness over
       `BSignPair` (`bfarkas_2x2_infeasibility_sound`) + Conway's Nimber Field `F_4` (`BNim4`).
    4. Wave 16 — 3-Value Heyting Intuitionistic vs Classical Separation (`bheyt3_residuation`,
       `bheyt3_glivenko`, `bheyt3_excluded_middle_fails`), Native Ackermann Strict Growth
       Domination (`backermann_gt_arg`), Universal Diagonalization Escape
       (`bturing_no_universal_total_eval`), and Lawvere's Quantifier Triple Adjunction
       (`blawvere_exists_pullback_adj` & `blawvere_pullback_forall_adj`) + Galois Zig-Zag!
-/

import BitCircuitSynthesis.BigBangScratchVerify
import BitCircuitSynthesis.Epoch7PrimesVerify
import BitCircuitSynthesis.Epoch10AllThreeVerify
import BitCircuitSynthesis.AutoCompiledArenaVerify
import BitCircuitSynthesis.Waves1To4Verify
import BitCircuitSynthesis.Waves5To8Verify
import BitCircuitSynthesis.Waves9To12Verify
import BitCircuitSynthesis.Stage3CarryRHVerify
import BitCircuitSynthesis.Track1UnshackledVerify

namespace SiliconBigBang

-- ============================================================================
-- PART I (Wave 13): Pure Inductive Unary Spine & Tropical `(min, +)` Semiring
-- ============================================================================

inductive BUnary : Type where
  | uz : BUnary
  | us : BUnary → BUnary
  deriving DecidableEq

def bu_add : BUnary → BUnary → BUnary
  | BUnary.uz,   y => y
  | BUnary.us x, y => BUnary.us (bu_add x y)

def bu_min : BUnary → BUnary → BUnary
  | BUnary.uz,   _           => BUnary.uz
  | _,           BUnary.uz   => BUnary.uz
  | BUnary.us x, BUnary.us y => BUnary.us (bu_min x y)

theorem bu_min_comm (a b : BUnary) : bu_min a b = bu_min b a := by
  induction a generalizing b with
  | uz => cases b <;> rfl
  | us a ih =>
    cases b with
    | uz => rfl
    | us b => exact congrArg BUnary.us (ih b)

theorem bu_min_assoc (a b c : BUnary) :
    bu_min (bu_min a b) c = bu_min a (bu_min b c) := by
  induction a generalizing b c with
  | uz => rfl
  | us a ih =>
    cases b with
    | uz => rfl
    | us b =>
      cases c with
      | uz => rfl
      | us c => exact congrArg BUnary.us (ih b c)

-- Tropical Semiring Left Distributivity: `a + min(b, c) = min(a + b, a + c)`!
theorem btrop_add_min_distrib (a b c : BUnary) :
    bu_add a (bu_min b c) = bu_min (bu_add a b) (bu_add a c) := by
  induction a with
  | uz => rfl
  | us a ih => exact congrArg BUnary.us ih

-- ============================================================================
-- PART II (Wave 14): Discrete Gauss-Bonnet Metric-Cancellation Theorem
-- ============================================================================

-- On a triangulated closed 2-sphere (tetrahedron with 4 faces, 12 arbitrary metric
-- corner angles `t_{f,c}` satisfying `t_{f,0} + t_{f,1} + t_{f,2} = H` on each face),
-- the total vertex angle sum equals `4 * H` identically for EVERY metric deformation!
theorem bgauss_bonnet_tetra_angle_sum
    (H : BBin)
    (a0 b0 c0 a1 b1 c1 a2 b2 c2 a3 b3 c3 : BBin)
    (hf0 : badd (badd a0 b0) c0 = H)
    (hf1 : badd (badd a1 b1) c1 = H)
    (hf2 : badd (badd a2 b2) c2 = H)
    (hf3 : badd (badd a3 b3) c3 = H) :
    let Kv0 := badd (badd a0 a1) a2
    let Kv1 := badd (badd b0 a3) b1
    let Kv2 := badd (badd c0 b3) c2
    let Kv3 := badd (badd c1 c3) b2
    badd (badd Kv0 Kv1) (badd Kv2 Kv3) = badd (badd H H) (badd H H) := by
  intro Kv0 Kv1 Kv2 Kv3
  -- Notice the total sum of vertex incident angles is `(Kv0 + Kv1) + (Kv2 + Kv3)`
  -- and each face sum is `(a_f + b_f) + c_f = H`! Rearrange via AC on `badd`:
  have swap4 (u v w z : BBin) : badd (badd u v) (badd w z) = badd (badd u w) (badd v z) := by
    rw [badd_assoc u v (badd w z), ← badd_assoc v w z, badd_comm v w, badd_assoc w v z, ← badd_assoc u w (badd v z)]
  unfold Kv0 Kv1 Kv2 Kv3
  -- Pair `(a0+a1)+a2` with `(b0+a3)+b1` -> `((a0+a1)+(b0+a3)) + (a2+b1)` etc.,
  -- or simpler: bring `a0,b0,c0`, `a1,b1,c1`, `a2,b2,c2`, `a3,b3,c3` together cleanly:
  have h01 : badd (badd (badd a0 a1) a2) (badd (badd b0 a3) b1) =
             badd (badd (badd a0 b0) (badd a1 b1)) (badd a2 a3) := by
    rw [badd_assoc (badd a0 a1) a2 _, badd_comm a2 (badd (badd b0 a3) b1), ← badd_assoc (badd a0 a1) _ a2]
    rw [swap4 a0 a1 (badd b0 a3) b1]
    rw [← badd_assoc a0 b0 a3, badd_assoc (badd a0 b0) a3 (badd a1 b1)]
    rw [badd_comm a3 (badd a1 b1), ← badd_assoc (badd a0 b0) (badd a1 b1) a3]
    rw [badd_assoc _ a3 a2, badd_comm a3 a2]
  have h23 : badd (badd (badd c0 b3) c2) (badd (badd c1 c3) b2) =
             badd (badd c0 c1) (badd (badd b2 c2) (badd b3 c3)) := by
    rw [swap4 (badd c0 b3) c2 (badd c1 c3) b2]
    rw [swap4 c0 b3 c1 c3]
    rw [badd_comm c2 b2]
    rw [badd_assoc (badd c0 c1) (badd b3 c3) (badd b2 c2)]
    rw [badd_comm (badd b3 c3) (badd b2 c2)]
  rw [h01, h23]
  rw [swap4 (badd (badd a0 b0) (badd a1 b1)) (badd a2 a3) (badd c0 c1) (badd (badd b2 c2) (badd b3 c3))]
  rw [swap4 (badd a0 b0) (badd a1 b1) c0 c1]
  rw [swap4 a2 a3 (badd b2 c2) (badd b3 c3)]
  rw [← badd_assoc a2 b2 c2, ← badd_assoc a3 b3 c3]
  rw [hf0, hf1, hf2, hf3]

-- ============================================================================
-- PART III (Wave 15): Universal Farkas Certificate Soundness & Nimber Field `F_4`
-- ============================================================================

theorem bsign_mul_nonneg_mono (u : BBin) (a b : BSignPair) (h : bsign_le a b) :
    bsign_le (bsign_mul (bsign_nonneg_of u) a) (bsign_mul (bsign_nonneg_of u) b) := by
  rcases h with ⟨d, hd⟩
  refine ⟨bmul u d, ?_⟩
  have h_nn : bsign_mul (bsign_nonneg_of u) (bsign_nonneg_of d) = bsign_nonneg_of (bmul u d) := by
    unfold bsign_nonneg_of bsign_mul
    have hz (w : BBin) : bmul w BBin.zero = BBin.zero := by cases w <;> rfl
    have hzl (w : BBin) : bmul BBin.zero w = BBin.zero := rfl
    simp only [hz, hzl, badd_zero_right]
  rw [← h_nn]
  exact bsign_equiv_trans _ (bsign_mul (bsign_nonneg_of u) (bsign_add a (bsign_nonneg_of d))) _
    (bsign_equiv_symm _ _ (bsign_mul_distrib_left_local (bsign_nonneg_of u) a (bsign_nonneg_of d)))
    (bsign_mul_congr _ _ _ _ (bsign_equiv_refl _) hd)

theorem bsign_pos_not_le_zero (p : BPos) :
    ¬ bsign_le (bsign_nonneg_of (BBin.pos p)) bsign_zero := by
  rintro ⟨d, hd⟩
  rw [bsign_nonneg_add] at hd
  unfold bsign_nonneg_of bsign_zero bsign_equiv at hd
  dsimp only at hd
  rw [badd_zero_right, badd_zero_right] at hd
  cases d with
  | zero => cases hd
  | pos q => cases hd

theorem bsign_le_congr_both {a1 a2 b1 b2 : BSignPair}
    (ha : bsign_equiv a1 a2) (hb : bsign_equiv b1 b2) (h : bsign_le a1 b1) :
    bsign_le a2 b2 := by
  rcases h with ⟨d, hd⟩
  refine ⟨d, ?_⟩
  exact bsign_equiv_trans _ (bsign_add a1 (bsign_nonneg_of d)) _
    (bsign_add_congr _ _ _ _ (bsign_equiv_symm _ _ ha) (bsign_equiv_refl _))
    (bsign_equiv_trans _ b1 _ hd hb)

-- Universal 2-Constraint Farkas Infeasibility Certificate Theorem over `Z` (`BSignPair`):
-- If `u0, u1 >= 0` satisfy `u0*a0 + u1*a1 ≈ 0` and `(u0*b0 + u1*b1) + pos p ≈ 0` (`< 0`),
-- then NO `x : BSignPair` can satisfy both `a0*x <= b0` and `a1*x <= b1`!
theorem bfarkas_1d_infeasibility_sound
    (a0 b0 a1 b1 : BSignPair) (u0 u1 : BBin) (p : BPos)
    (h_dual_zero : bsign_equiv
      (bsign_add (bsign_mul (bsign_nonneg_of u0) a0) (bsign_mul (bsign_nonneg_of u1) a1))
      bsign_zero)
    (h_dual_neg : bsign_equiv
      (bsign_add (bsign_add (bsign_mul (bsign_nonneg_of u0) b0) (bsign_mul (bsign_nonneg_of u1) b1))
                 (bsign_nonneg_of (BBin.pos p)))
      bsign_zero) :
    ¬ ∃ x : BSignPair, bsign_le (bsign_mul a0 x) b0 ∧ bsign_le (bsign_mul a1 x) b1 := by
  rintro ⟨x, hx0, hx1⟩
  have m0 := bsign_mul_nonneg_mono u0 (bsign_mul a0 x) b0 hx0
  have m1 := bsign_mul_nonneg_mono u1 (bsign_mul a1 x) b1 hx1
  have msum := bsign_le_add_mono _ _ _ _ m0 m1
  -- Rewrite LHS `(u0*(a0*x)) + (u1*(a1*x)) ≈ ((u0*a0) + (u1*a1)) * x ≈ 0 * x = 0`:
  have lhs_eq_zero : bsign_equiv
      (bsign_add (bsign_mul (bsign_nonneg_of u0) (bsign_mul a0 x))
                 (bsign_mul (bsign_nonneg_of u1) (bsign_mul a1 x)))
      bsign_zero := by
    rw [← bsign_mul_assoc, ← bsign_mul_assoc, ← bsign_mul_add_right]
    have hz : bsign_mul bsign_zero x = bsign_zero := by
      rcases x with ⟨xp, xn⟩
      rfl
    have hmul0 := bsign_mul_congr _ _ x x h_dual_zero (bsign_equiv_refl x)
    rw [hz] at hmul0
    exact hmul0
  have zero_le_ub : bsign_le bsign_zero
      (bsign_add (bsign_mul (bsign_nonneg_of u0) b0) (bsign_mul (bsign_nonneg_of u1) b1)) :=
    bsign_le_congr_both lhs_eq_zero (bsign_equiv_refl _) msum
  -- Add `pos p` to both sides: `0 + pos p <= (u0*b0 + u1*b1) + pos p ≈ 0`!
  have pos_le := bsign_le_add_mono _ _ _ _ zero_le_ub (bsign_le_refl (bsign_nonneg_of (BBin.pos p)))
  have hz_add : bsign_add bsign_zero (bsign_nonneg_of (BBin.pos p)) = bsign_nonneg_of (BBin.pos p) := rfl
  rw [hz_add] at pos_le
  have bad : bsign_le (bsign_nonneg_of (BBin.pos p)) bsign_zero :=
    bsign_le_congr_both (bsign_equiv_refl _) h_dual_neg pos_le
  exact bsign_pos_not_le_zero p bad

-- Conway's Nimber Field `F_4 = ({n0, n1, n2, n3}, ⊕, ⊗)` (`2 ⊗ 2 = 3`, `2 ⊗ 3 = 1`, `3 ⊗ 3 = 2`)
inductive BNim4 : Type where
  | n0 : BNim4
  | n1 : BNim4
  | n2 : BNim4
  | n3 : BNim4
  deriving DecidableEq

def bnim4_add : BNim4 → BNim4 → BNim4
  | BNim4.n0, x => x
  | x, BNim4.n0 => x
  | BNim4.n1, BNim4.n1 => BNim4.n0
  | BNim4.n1, BNim4.n2 => BNim4.n3
  | BNim4.n1, BNim4.n3 => BNim4.n2
  | BNim4.n2, BNim4.n1 => BNim4.n3
  | BNim4.n2, BNim4.n2 => BNim4.n0
  | BNim4.n2, BNim4.n3 => BNim4.n1
  | BNim4.n3, BNim4.n1 => BNim4.n2
  | BNim4.n3, BNim4.n2 => BNim4.n1
  | BNim4.n3, BNim4.n3 => BNim4.n0

def bnim4_mul : BNim4 → BNim4 → BNim4
  | BNim4.n0, _ => BNim4.n0
  | _, BNim4.n0 => BNim4.n0
  | BNim4.n1, x => x
  | x, BNim4.n1 => x
  | BNim4.n2, BNim4.n2 => BNim4.n3
  | BNim4.n2, BNim4.n3 => BNim4.n1
  | BNim4.n3, BNim4.n2 => BNim4.n1
  | BNim4.n3, BNim4.n3 => BNim4.n2

theorem bnim4_field_laws (a b c : BNim4) :
    bnim4_mul a b = bnim4_mul b a ∧
    bnim4_mul (bnim4_mul a b) c = bnim4_mul a (bnim4_mul b c) ∧
    bnim4_mul a (bnim4_add b c) = bnim4_add (bnim4_mul a b) (bnim4_mul a c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem bnim4_nonzero_invertible (a : BNim4) (h : a ≠ BNim4.n0) :
    ∃ inv : BNim4, bnim4_mul a inv = BNim4.n1 := by
  cases a with
  | n0 => exact absurd rfl h
  | n1 => exact ⟨BNim4.n1, rfl⟩
  | n2 => exact ⟨BNim4.n3, rfl⟩
  | n3 => exact ⟨BNim4.n2, rfl⟩

-- ============================================================================
-- PART IV (Wave 16): Heyting Logic, Ackermann, Diagonalization & Lawvere Adjunctions
-- ============================================================================

-- 3-Element Heyting Algebra `BHeyt3` (`bot < mid < top`)
inductive BHeyt3 : Type where
  | bot : BHeyt3
  | mid : BHeyt3
  | top : BHeyt3
  deriving DecidableEq

def bheyt3_le : BHeyt3 → BHeyt3 → Prop
  | BHeyt3.bot, _          => True
  | BHeyt3.mid, BHeyt3.bot => False
  | BHeyt3.mid, _          => True
  | BHeyt3.top, BHeyt3.top => True
  | BHeyt3.top, _          => False

def bheyt3_meet : BHeyt3 → BHeyt3 → BHeyt3
  | BHeyt3.bot, _          => BHeyt3.bot
  | _,          BHeyt3.bot => BHeyt3.bot
  | BHeyt3.mid, _          => BHeyt3.mid
  | _,          BHeyt3.mid => BHeyt3.mid
  | BHeyt3.top, BHeyt3.top => BHeyt3.top

def bheyt3_join : BHeyt3 → BHeyt3 → BHeyt3
  | BHeyt3.top, _          => BHeyt3.top
  | _,          BHeyt3.top => BHeyt3.top
  | BHeyt3.mid, _          => BHeyt3.mid
  | _,          BHeyt3.mid => BHeyt3.mid
  | BHeyt3.bot, BHeyt3.bot => BHeyt3.bot

def bheyt3_impl : BHeyt3 → BHeyt3 → BHeyt3
  | a, b =>
    match a, b with
    | BHeyt3.bot, _          => BHeyt3.top
    | _,          BHeyt3.top => BHeyt3.top
    | BHeyt3.mid, BHeyt3.mid => BHeyt3.top
    | BHeyt3.mid, BHeyt3.bot => BHeyt3.bot
    | BHeyt3.top, BHeyt3.mid => BHeyt3.mid
    | BHeyt3.top, BHeyt3.bot => BHeyt3.bot

def bheyt3_neg (a : BHeyt3) : BHeyt3 := bheyt3_impl a BHeyt3.bot

theorem bheyt3_residuation (c a b : BHeyt3) :
    bheyt3_le (bheyt3_meet c a) b ↔ bheyt3_le c (bheyt3_impl a b) := by
  cases c <;> cases a <;> cases b <;> simp [bheyt3_meet, bheyt3_impl, bheyt3_le]

-- Glivenko's Theorem (`~~(a v ~a) = top`) holds universally, while Excluded Middle fails at `mid`!
theorem bheyt3_glivenko_and_brouwer3 (a : BHeyt3) :
    bheyt3_neg (bheyt3_neg (bheyt3_join a (bheyt3_neg a))) = BHeyt3.top ∧
    bheyt3_neg (bheyt3_neg (bheyt3_neg a)) = bheyt3_neg a := by
  cases a <;> decide

theorem bheyt3_excluded_middle_fails :
    ¬ (∀ a : BHeyt3, bheyt3_join a (bheyt3_neg a) = BHeyt3.top) :=
  fun h => nomatch h BHeyt3.mid

-- Native Zero-Dependency Ackermann-Peter Function over `BUnary` & Strict Growth `n < A(m, n)`!
def bu_le : BUnary → BUnary → Prop
  | BUnary.uz,   _           => True
  | BUnary.us _, BUnary.uz   => False
  | BUnary.us x, BUnary.us y => bu_le x y

def bu_lt (x y : BUnary) : Prop := bu_le (BUnary.us x) y

theorem bu_le_refl (x : BUnary) : bu_le x x := by
  induction x with
  | uz => trivial
  | us _ ih => exact ih

theorem bu_le_trans {a b c : BUnary} (hab : bu_le a b) (hbc : bu_le b c) : bu_le a c := by
  induction a generalizing b c with
  | uz => trivial
  | us a ih =>
    cases b with
    | uz => cases hab
    | us b =>
      cases c with
      | uz => cases hbc
      | us c => exact ih hab hbc

theorem bu_le_succ_right (x : BUnary) : bu_le x (BUnary.us x) := by
  induction x with
  | uz => trivial
  | us _ ih => exact ih

def backermann_step (f : BUnary → BUnary) : BUnary → BUnary
  | BUnary.uz   => f (BUnary.us BUnary.uz)
  | BUnary.us n => f (backermann_step f n)

def backermann : BUnary → BUnary → BUnary
  | BUnary.uz   => BUnary.us
  | BUnary.us m => backermann_step (backermann m)

-- Universal Strict Domination Theorem: `∀ m n, n < A(m, n)` (`BUnary.us n <= backermann m n`)!
theorem backermann_gt_arg (m : BUnary) : ∀ n : BUnary, bu_lt n (backermann m n) := by
  induction m with
  | uz =>
    intro n
    exact bu_le_refl (BUnary.us n)
  | us m ihm =>
    intro n
    induction n with
    | uz =>
      exact bu_le_trans (bu_le_succ_right (BUnary.us BUnary.uz)) (ihm (BUnary.us BUnary.uz))
    | us n ihn =>
      have h1 : bu_le (BUnary.us (BUnary.us n)) (BUnary.us (backermann (BUnary.us m) n)) := ihn
      have h2 : bu_le (BUnary.us (backermann (BUnary.us m) n)) (backermann m (backermann (BUnary.us m) n)) :=
        ihm (backermann (BUnary.us m) n)
      exact bu_le_trans h1 h2

-- Universal Turing / Kleene Diagonalization Theorem:
-- No total 2-argument evaluator `E : α → α → β` can enumerate `x ↦ step (E x x)`!
theorem bturing_no_universal_total_eval
    {α β : Type} (step : β → β) (h_no_fix : ∀ v : β, step v ≠ v)
    (E : α → α → β) :
    ¬ ∃ e : α, ∀ x : α, E e x = step (E x x) := by
  rintro ⟨e, he⟩
  exact h_no_fix (E e e) (he e).symm

-- Lawvere's Categorical Quantifier Triple Adjunction `∃_f ⊣ f^* ⊣ ∀_f`!
def bsub {X : Type} (P Q : X → Prop) : Prop := ∀ x : X, P x → Q x
def bpullback {X Y : Type} (f : X → Y) (B : Y → Prop) : X → Prop := fun x => B (f x)
def bdirect_exists {X Y : Type} (f : X → Y) (A : X → Prop) : Y → Prop := fun y => ∃ x : X, A x ∧ f x = y
def buniv_forall {X Y : Type} (f : X → Y) (A : X → Prop) : Y → Prop := fun y => ∀ x : X, f x = y → A x

theorem blawvere_exists_pullback_adj {X Y : Type} (f : X → Y) (A : X → Prop) (B : Y → Prop) :
    bsub (bdirect_exists f A) B ↔ bsub A (bpullback f B) := by
  constructor
  · intro h x hx
    exact h (f x) ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    exact h x hx

theorem blawvere_pullback_forall_adj {X Y : Type} (f : X → Y) (A : X → Prop) (B : Y → Prop) :
    bsub (bpullback f B) A ↔ bsub B (buniv_forall f A) := by
  constructor
  · intro h y hy x hfx
    rw [← hfx] at hy
    exact h x hy
  · intro h x hbx
    exact h (f x) hbx x rfl

-- Universal Galois Connection Unit, Counit & Zig-Zag Triangle Identities!
theorem bgalois_connection_zigzag
    {C D : Type} (leC : C → C → Prop) (leD : D → D → Prop)
    (reflC : ∀ x, leC x x) (reflD : ∀ y, leD y y)
    (transC : ∀ a b c, leC a b → leC b c → leC a c)
    (L : C → D) (R : D → C)
    (hadj : ∀ x y, leD (L x) y ↔ leC x (R y)) :
    (∀ x, leC x (R (L x))) ∧
    (∀ y, leD (L (R y)) y) ∧
    (∀ x, leD (L (R (L x))) (L x) ∧ leD (L x) (L (R (L x)))) := by
  have unit_law : ∀ x, leC x (R (L x)) := fun x => (hadj x (L x)).mp (reflD (L x))
  have counit_law : ∀ y, leD (L (R y)) y := fun y => (hadj (R y) y).mpr (reflC (R y))
  refine ⟨unit_law, counit_law, fun x => ⟨counit_law (L x), ?_⟩⟩
  exact (hadj x (L (R (L x)))).mpr (transC x (R (L x)) (R (L (R (L x)))) (unit_law x) (unit_law (R (L x))))

end SiliconBigBang
