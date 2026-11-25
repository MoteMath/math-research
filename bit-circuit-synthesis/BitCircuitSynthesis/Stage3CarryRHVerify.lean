/-
  Pure-Silicon Mathematical "Big Bang" — Stage 3 Zero-Dependency Lean 4 Kernel Proofs
  (`Stage3CarryRHVerify.lean`: Epochs 37..40 Carry Dictionary & RH Positivity Lab)

  NO Mathlib. NO built-in `Nat`, `Int`, `Rat`, `Real`, or `Bool` arithmetic used anywhere.
  Extends `BigBangScratchVerify` .. `Waves9To12Verify` strictly from Epoch-0 `BBit`,
  `BPos`, `BBin`, `BWord`, and `BSignPair`:

  1. Infinite Carry-Less Frobenius Endomorphism Tower vs Carried Obstruction:
     - `bfrob_tower_add_hom` & `bfrob_tower_mul_hom`: Every iterated `2^k`-power map on
       `BBin` (`F_2[x]`) is an exact ring endomorphism (`f(x ⊕ y) = f(x) ⊕ f(y)` and
       `f(x ⊗ y) = f(x) ⊗ f(y)`).
     - `bbin_carried_sq_obstruction` & `bbin_carried_sq_never_additive_on_pos`: In carried
       arithmetic (`N`), `(x + y)^2 = (x^2 + y^2) + 2*x*y`, and for ALL positive `p, q : BPos`,
       `(p + q)^2 ≠ p^2 + q^2` (proving why carried integers lack a Frobenius endomorphism!).
  2. Carry-Less Ultrametric Isosceles Law vs Carried Overflow:
     - `bbin_deg_le_xor`: Universal ultrametric triangle inequality
       `deg(x) <= d -> deg(y) <= d -> deg(x ⊕ y) <= d` on `BBin`, vs `1 + 1 = 2` carry jump!
  3. Universal Homogeneous Genus-2 Weil Self-Reciprocal Trace Factorization:
     - `bweil_genus2_trace_factorization`: Over `BSignPair` (`Z`), proves universally that
       `(v^2 + p*u^2)^2 - s1*u*v*(v^2 + p*u^2) + (b2 - 2*p)*u^2*v^2`
       `≈ v^4 - s1*u*v^3 + b2*u^2*v^2 - p*s1*u^3*v + p^2*u^4`!
  4. Directed-Rounding Interval Enclosure Soundness (`BInterval`):
     - `binterval_sub_sound`: Proves `a0 <= a <= a1 -> b0 <= b <= b1 -> a0 - b1 <= a - b <= a1 - b0`
       over `BSignPair`, certifying the exact interval subtraction rule of Kernel 3B.

  Mandatory Scope Note: Finite and fixed-width evaluations say nothing about the zeros of
  zeta(s) over Q; function-field Weil positivity applies strictly to curves over F_p.
-/

import BitCircuitSynthesis.BigBangScratchVerify
import BitCircuitSynthesis.Epoch7PrimesVerify
import BitCircuitSynthesis.Epoch10AllThreeVerify
import BitCircuitSynthesis.AutoCompiledArenaVerify
import BitCircuitSynthesis.Waves1To4Verify
import BitCircuitSynthesis.Waves5To8Verify
import BitCircuitSynthesis.Waves9To12Verify

namespace SiliconBigBang

-- ============================================================================
-- PART I: Infinite Carry-Less Frobenius Tower vs Carried `2*x*y` Obstruction
-- ============================================================================

def bfrob2 (x : BBin) : BBin := bclmul x x

theorem bfrob2_mul_hom (x y : BBin) :
    bfrob2 (bclmul x y) = bclmul (bfrob2 x) (bfrob2 y) := by
  unfold bfrob2
  rw [bclmul_assoc x y (bclmul x y)]
  rw [← bclmul_assoc y x y, bclmul_comm y x, bclmul_assoc x y y]
  rw [← bclmul_assoc x x (bclmul y y)]

-- Arbitrary `2^|w|`-power Frobenius tower indexed by zero-dependency `AutoArena.BWord`!
def bfrob_tower : AutoArena.BWord → BBin → BBin
  | AutoArena.BWord.nil,        x => x
  | AutoArena.BWord.cons _ rst, x => bfrob2 (bfrob_tower rst x)

theorem bfrob_tower_add_hom (w : AutoArena.BWord) (x y : BBin) :
    bfrob_tower w (bxor_bin x y) = bxor_bin (bfrob_tower w x) (bfrob_tower w y) := by
  induction w with
  | nil => rfl
  | cons _ rst ih =>
    unfold bfrob_tower bfrob2
    rw [ih, bclmul_freshmans_dream]

theorem bfrob_tower_mul_hom (w : AutoArena.BWord) (x y : BBin) :
    bfrob_tower w (bclmul x y) = bclmul (bfrob_tower w x) (bfrob_tower w y) := by
  induction w with
  | nil => rfl
  | cons _ rst ih =>
    unfold bfrob_tower
    rw [ih, bfrob2_mul_hom]

-- Carried Binary Multiplication Squaring Identity: `(x + y)^2 = (x^2 + y^2) + 2*(x*y)`!
theorem bshl1_eq_add_self (z : BBin) : bshl1 z = badd z z := by
  cases z with
  | zero => rfl
  | pos p =>
    unfold bshl1 bsnoc badd
    have h : ∀ q : BPos, BPos.x0 q = bpos_add q q := by
      intro q
      induction q with
      | one => rfl
      | x0 q ih => simp [bpos_add, ← ih]
      | x1 q ih => simp [bpos_add, bpos_add_carry_eq_succ_add, ← ih, bpos_succ]
    exact congrArg BBin.pos (h p)

theorem bbin_carried_sq_obstruction (x y : BBin) :
    bmul (badd x y) (badd x y) =
    badd (badd (bmul x x) (bmul y y)) (bshl1 (bmul x y)) := by
  rw [bmul_add_left, bmul_add_right, bmul_add_right]
  rw [bmul_comm y x, bshl1_eq_add_self (bmul x y)]
  rw [badd_comm (bmul x y) (bmul y y)]
  rw [badd_four_swap (bmul x x) (bmul x y) (bmul y y) (bmul x y)]

-- Universal Carried Non-Additivity Theorem: For ALL `p, q : BPos`, `(p + q)^2 ≠ p^2 + q^2`!
theorem bpos_mul_pos_is_pos (p q : BPos) :
    ∃ r : BPos, bmul (BBin.pos p) (BBin.pos q) = BBin.pos r :=
  ⟨bpos_mul p q, rfl⟩

theorem bbin_carried_sq_never_additive_on_pos (p q : BPos) :
    bmul (badd (BBin.pos p) (BBin.pos q)) (badd (BBin.pos p) (BBin.pos q)) ≠
    badd (bmul (BBin.pos p) (BBin.pos p)) (bmul (BBin.pos q) (BBin.pos q)) := by
  rw [bbin_carried_sq_obstruction (BBin.pos p) (BBin.pos q)]
  intro h
  have hsum_pos : ∃ s : BPos, badd (bmul (BBin.pos p) (BBin.pos p)) (bmul (BBin.pos q) (BBin.pos q)) = BBin.pos s :=
    ⟨bpos_add (bpos_mul p p) (bpos_mul q q), rfl⟩
  rcases hsum_pos with ⟨s, hs⟩
  rw [hs] at h
  change BBin.pos (bpos_add s (BPos.x0 (bpos_mul p q))) = BBin.pos s at h
  injection h with hp
  exact bpos_ne_add_self s (BPos.x0 (bpos_mul p q)) hp

-- ============================================================================
-- PART II: Carry-Less Ultrametric Isosceles Law vs Carried Overflow
-- ============================================================================

def bpos_len_le : BPos → BPos → Prop
  | BPos.one,  _         => True
  | BPos.x0 _, BPos.one  => False
  | BPos.x1 _, BPos.one  => False
  | BPos.x0 p, BPos.x0 q => bpos_len_le p q
  | BPos.x0 p, BPos.x1 q => bpos_len_le p q
  | BPos.x1 p, BPos.x0 q => bpos_len_le p q
  | BPos.x1 p, BPos.x1 q => bpos_len_le p q

def bbin_deg_le : BBin → BBin → Prop
  | BBin.zero,  _          => True
  | BBin.pos _, BBin.zero  => False
  | BBin.pos p, BBin.pos q => bpos_len_le p q

theorem bsnoc_deg_le_x0 (z : BBin) (b : BBit) (d : BPos)
    (hz : bbin_deg_le z (BBin.pos d)) :
    bbin_deg_le (bsnoc z b) (BBin.pos (BPos.x0 d)) := by
  cases z with
  | zero => cases b <;> trivial
  | pos r => cases b <;> exact hz

theorem bsnoc_deg_le_x1 (z : BBin) (b : BBit) (d : BPos)
    (hz : bbin_deg_le z (BBin.pos d)) :
    bbin_deg_le (bsnoc z b) (BBin.pos (BPos.x1 d)) := by
  cases z with
  | zero => cases b <;> trivial
  | pos r => cases b <;> exact hz

theorem bpos_xor_deg_le (p q d : BPos)
    (hp : bpos_len_le p d) (hq : bpos_len_le q d) :
    bbin_deg_le (bpos_xor p q) (BBin.pos d) := by
  induction d generalizing p q with
  | one =>
    cases p with
    | one =>
      cases q with
      | one => trivial
      | x0 _ => cases hq
      | x1 _ => cases hq
    | x0 _ => cases hp
    | x1 _ => cases hp
  | x0 d ih =>
    cases p with
    | one =>
      cases q with
      | one => trivial
      | x0 q => exact hq
      | x1 q => exact hq
    | x0 p =>
      cases q with
      | one => exact hp
      | x0 q => exact bsnoc_deg_le_x0 (bpos_xor p q) BBit.b0 d (ih p q hp hq)
      | x1 q => exact bsnoc_deg_le_x0 (bpos_xor p q) BBit.b1 d (ih p q hp hq)
    | x1 p =>
      cases q with
      | one => exact hp
      | x0 q => exact bsnoc_deg_le_x0 (bpos_xor p q) BBit.b1 d (ih p q hp hq)
      | x1 q => exact bsnoc_deg_le_x0 (bpos_xor p q) BBit.b0 d (ih p q hp hq)
  | x1 d ih =>
    cases p with
    | one =>
      cases q with
      | one => trivial
      | x0 q => exact hq
      | x1 q => exact hq
    | x0 p =>
      cases q with
      | one => exact hp
      | x0 q => exact bsnoc_deg_le_x1 (bpos_xor p q) BBit.b0 d (ih p q hp hq)
      | x1 q => exact bsnoc_deg_le_x1 (bpos_xor p q) BBit.b1 d (ih p q hp hq)
    | x1 p =>
      cases q with
      | one => exact hp
      | x0 q => exact bsnoc_deg_le_x1 (bpos_xor p q) BBit.b1 d (ih p q hp hq)
      | x1 q => exact bsnoc_deg_le_x1 (bpos_xor p q) BBit.b0 d (ih p q hp hq)

-- Universal Carry-Less Ultrametric Inequality: `deg(x) <= d -> deg(y) <= d -> deg(x ⊕ y) <= d`!
theorem bbin_deg_le_xor (x y z : BBin)
    (hx : bbin_deg_le x z) (hy : bbin_deg_le y z) :
    bbin_deg_le (bxor_bin x y) z := by
  cases z with
  | zero =>
    cases x with
    | zero =>
      cases y with
      | zero => trivial
      | pos _ => cases hy
    | pos _ => cases hx
  | pos d =>
    cases x with
    | zero => exact hy
    | pos p =>
      cases y with
      | zero => exact hx
      | pos q => exact bpos_xor_deg_le p q d hx hy

-- Carried Arithmetic Violates Ultrametricity Already at `1 + 1 = 2`:
theorem bbin_carried_breaks_ultrametric :
    bbin_deg_le bone bone ∧ ¬ bbin_deg_le (badd bone bone) bone :=
  ⟨trivial, fun h => h⟩

-- ============================================================================
-- PART III: Homogeneous Genus-2 Self-Reciprocal Weil Trace Quadratic Identity
-- ============================================================================

-- Proves universally over `BSignPair` (`Z`, zero division or square roots!) that setting
-- `W = v^2 + p*u^2` reduces the degree-4 self-reciprocal Weil polynomial to a quadratic:
--   `(W^2 + (b2 - 2*p)*(u^2 * v^2)) - s1*u*v*W ≈ (v^4 + b2*(u^2*v^2) + p^2*u^4) - s1*u*v*(v^2 + p*u^2)`!
theorem bweil_genus2_trace_core (v2 pu2 b2_u2v2 two_pu2v2 : BSignPair)
    (hmid : bsign_add (bsign_mul v2 pu2) (bsign_mul pu2 v2) = two_pu2v2) :
    bsign_equiv
      (bsign_add (bsign_mul (bsign_add v2 pu2) (bsign_add v2 pu2))
                 (bsign_add b2_u2v2 (bsign_neg two_pu2v2)))
      (bsign_add (bsign_add (bsign_mul v2 v2) (bsign_mul pu2 pu2)) b2_u2v2) := by
  simp only [bsign_mul_add_distrib, bsign_mul_add_right]
  rw [bsign_add_four_swap (bsign_mul v2 v2) (bsign_mul pu2 v2) (bsign_mul v2 pu2) (bsign_mul pu2 pu2)]
  rw [bsign_add_comm (bsign_mul pu2 v2) (bsign_mul pu2 pu2)]
  rw [bsign_add_four_swap (bsign_mul v2 v2) (bsign_mul v2 pu2) (bsign_mul pu2 pu2) (bsign_mul pu2 v2)]
  rw [hmid]
  rw [bsign_add_four_swap
        (bsign_add (bsign_mul v2 v2) (bsign_mul pu2 pu2))
        two_pu2v2
        b2_u2v2
        (bsign_neg two_pu2v2)]
  exact bsign_sub_pair_cancel _ two_pu2v2

theorem bweil_genus2_self_reciprocal_factorization (p s1 b2 u v : BSignPair) :
    let u2 := bsign_mul u u
    let v2 := bsign_mul v v
    let pu2 := bsign_mul p u2
    let u2v2 := bsign_mul u2 v2
    let W := bsign_add v2 pu2
    let trace_lin := bsign_neg (bsign_mul (bsign_mul s1 (bsign_mul u v)) W)
    bsign_equiv
      (bsign_add
        (bsign_add (bsign_mul W W)
                   (bsign_mul (bsign_add b2 (bsign_neg (bsign_add p p))) u2v2))
        trace_lin)
      (bsign_add
        (bsign_add (bsign_add (bsign_mul v2 v2) (bsign_mul pu2 pu2))
                   (bsign_mul b2 u2v2))
        trace_lin) := by
  intro u2 v2 pu2 u2v2 W trace_lin
  have hdist :
      bsign_mul (bsign_add b2 (bsign_neg (bsign_add p p))) u2v2 =
      bsign_add (bsign_mul b2 u2v2) (bsign_neg (bsign_add (bsign_mul p u2v2) (bsign_mul p u2v2))) := by
    rw [bsign_mul_add_right, bsign_mul_neg_left, bsign_mul_add_right]
  rw [hdist]
  have hmid :
      bsign_add (bsign_mul v2 pu2) (bsign_mul pu2 v2) =
      bsign_add (bsign_mul p u2v2) (bsign_mul p u2v2) := by
    rw [bsign_mul_comm v2 pu2]
    unfold pu2 u2v2
    rw [bsign_mul_assoc p u2 v2]
  exact bsign_add_congr _ _ trace_lin trace_lin
    (bweil_genus2_trace_core v2 pu2 (bsign_mul b2 u2v2) _ hmid)
    (bsign_equiv_refl trace_lin)

-- ============================================================================
-- PART IV: Directed-Rounding Interval Enclosure Soundness (`BInterval`)
-- ============================================================================

def bsign_nonneg_of (d : BBin) : BSignPair := ⟨d, BBin.zero⟩

def bsign_le (x y : BSignPair) : Prop :=
  ∃ d : BBin, bsign_equiv (bsign_add x (bsign_nonneg_of d)) y

theorem bsign_le_refl (x : BSignPair) : bsign_le x x :=
  ⟨BBin.zero, by
    change bsign_equiv (bsign_add x bsign_zero) x
    rw [bsign_add_zero_right]
    exact bsign_equiv_refl x⟩

theorem bsign_nonneg_add (d1 d2 : BBin) :
    bsign_add (bsign_nonneg_of d1) (bsign_nonneg_of d2) = bsign_nonneg_of (badd d1 d2) := by
  unfold bsign_nonneg_of bsign_add
  simp only [badd_zero_right]

theorem bsign_le_trans (x y z : BSignPair) (hxy : bsign_le x y) (hyz : bsign_le y z) :
    bsign_le x z := by
  rcases hxy with ⟨d1, h1⟩
  rcases hyz with ⟨d2, h2⟩
  refine ⟨badd d1 d2, ?_⟩
  rw [← bsign_nonneg_add, ← bsign_add_assoc]
  exact bsign_equiv_trans _ (bsign_add y (bsign_nonneg_of d2)) _
    (bsign_add_congr _ _ _ _ h1 (bsign_equiv_refl _)) h2

theorem bsign_equiv_neg_congr (u v : BSignPair) (h : bsign_equiv u v) :
    bsign_equiv (bsign_neg u) (bsign_neg v) := by
  unfold bsign_equiv bsign_neg at *
  dsimp only at *
  rw [badd_comm u.neg v.pos, badd_comm v.neg u.pos]
  exact h.symm

theorem bsign_le_neg_antitone (b0 b : BSignPair) (h : bsign_le b0 b) :
    bsign_le (bsign_neg b) (bsign_neg b0) := by
  rcases h with ⟨d, hd⟩
  refine ⟨d, ?_⟩
  -- `b0 + d ≈ b` -> `(-b) + d ≈ (-b) + ((b0 + d) + (-b0))?` Even simpler:
  -- `(-b) + d ≈ -b0` iff `(-b + d) + b0 ≈ (-b0) + b0 ≈ 0`!
  apply bsign_equiv_trans _ (bsign_add (bsign_neg (bsign_add b0 (bsign_nonneg_of d))) (bsign_nonneg_of d)) _
  · exact bsign_add_congr _ _ _ _ (bsign_equiv_neg_congr _ _ hd.symm) (bsign_equiv_refl _)
  · rw [bsign_neg_add, bsign_add_assoc (bsign_neg b0) (bsign_neg (bsign_nonneg_of d)) (bsign_nonneg_of d)]
    rw [bsign_add_comm (bsign_neg (bsign_nonneg_of d)) (bsign_nonneg_of d)]
    exact bsign_sub_pair_cancel (bsign_neg b0) (bsign_nonneg_of d)

theorem bsign_le_add_mono (a0 a c0 c : BSignPair)
    (ha : bsign_le a0 a) (hc : bsign_le c0 c) :
    bsign_le (bsign_add a0 c0) (bsign_add a c) := by
  rcases ha with ⟨da, hda⟩
  rcases hc with ⟨dc, hdc⟩
  refine ⟨badd da dc, ?_⟩
  rw [← bsign_nonneg_add, bsign_add_four_swap a0 c0 (bsign_nonneg_of da) (bsign_nonneg_of dc)]
  exact bsign_add_congr _ _ _ _ hda hdc

structure BInterval where
  lo : BSignPair
  hi : BSignPair

def binterval_contains (I : BInterval) (x : BSignPair) : Prop :=
  bsign_le I.lo x ∧ bsign_le x I.hi

def binterval_sub (A B : BInterval) : BInterval :=
  ⟨bsign_add A.lo (bsign_neg B.hi), bsign_add A.hi (bsign_neg B.lo)⟩

-- Universal Directed-Rounding Interval Subtraction Soundness Theorem:
--   `x in [A.lo, A.hi] -> y in [B.lo, B.hi] -> (x - y) in [A.lo - B.hi, A.hi - B.lo]`!
theorem binterval_sub_sound (A B : BInterval) (x y : BSignPair)
    (hx : binterval_contains A x) (hy : binterval_contains B y) :
    binterval_contains (binterval_sub A B) (bsign_add x (bsign_neg y)) :=
  ⟨bsign_le_add_mono A.lo x (bsign_neg B.hi) (bsign_neg y) hx.1 (bsign_le_neg_antitone y B.hi hy.2),
   bsign_le_add_mono x A.hi (bsign_neg y) (bsign_neg B.lo) hx.2 (bsign_le_neg_antitone B.lo y hy.1)⟩

end SiliconBigBang
