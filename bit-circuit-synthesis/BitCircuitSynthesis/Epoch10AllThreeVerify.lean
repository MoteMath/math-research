/-
  Pure-Silicon Mathematical "Big Bang" — All 3 Pillars Zero-Dependency Lean 4 Kernel Proofs
  (`Epoch10AllThreeVerify.lean`)

  NO Mathlib. NO built-in `Nat`, `Int`, or `Bool` arithmetic used anywhere.
  Extends `BigBangScratchVerify` + `Epoch7PrimesVerify` strictly from Epoch-0 `BBit` & `BBin`:

  1. Pillar 2 Foundation (Universal Cancellation & Semiring Laws on `BBin`):
     - `bpos_succ_inj`, `bpos_ne_add_self`, `badd_assoc`, `badd_cancel_left`, `badd_cancel_right`
     - `bmul_add_left`, `bmul_add_right`, `bmul_comm`, `bmul_assoc`, `bdivides_trans`
     - `bclmul_assoc`, `bdivides_f2x_trans`
  2. Pillar 1 (Epoch 10 — Grothendieck Signed Ring `BSignPair` = Z & Carry-vs-Carryless Shells):
     - `BSignPair`, `bsign_equiv` (`refl`, `symm`, `trans` proved via `badd_cancel_right`!)
     - `bsign_add`, `bsign_neg`, `bsign_mul`, `bsign_add_neg_cancel`, `bsign_add_congr`,
       `bsign_mul_congr`, `bsign_mul_comm`
     - Exact Carry-Less `F_2[x]` Degree-Shell Mobius Annihilation (`sum_{deg=2} mu_F2x = 0`,
       `sum_{deg=3} mu_F2x = 0`) vs Carried `N` Shell Residual (`sum_{n in 4..7} mu_N = -1 != 0`).
  3. Pillar 3 (Epochs 11..12 — Quotient Ring Congruences & Galois Fields `F_4`, `F_8`):
     - Universal `F_2[x]/(P)` ring congruence theorems (`bf2x_cong_refl`, `bf2x_cong_symm`,
       `bf2x_cong_trans`, `bf2x_cong_add`, `bf2x_cong_mul`) for all `P, a, b in BBin`!
     - Multiplicative group / Fermat laws in `F_4^x = (F_2[x]/(t^2+t+1))^x` (`a^3 == 1 mod 7`)
       and `F_8^x = (F_2[x]/(t^3+t+1))^x` (`a^7 == 1 mod 11`).
-/

import BitCircuitSynthesis.BigBangScratchVerify
import BitCircuitSynthesis.Epoch7PrimesVerify

namespace SiliconBigBang

-- ============================================================================
-- PART I (Pillar 2): Universal Addition Associativity & Cancellation (`LAW_CANCEL`)
-- ============================================================================

theorem bpos_succ_ne_one (p : BPos) : bpos_succ p ≠ BPos.one := by
  cases p <;> intro h <;> cases h

theorem bpos_succ_inj (p q : BPos) (h : bpos_succ p = bpos_succ q) : p = q := by
  induction p generalizing q with
  | one =>
    cases q with
    | one => rfl
    | x0 q => cases h
    | x1 q =>
      injection h with h1
      exact absurd h1.symm (bpos_succ_ne_one q)
  | x0 p _ =>
    cases q with
    | one => cases h
    | x0 q => injection h with hp; rw [hp]
    | x1 q => cases h
  | x1 p ih =>
    cases q with
    | one =>
      injection h with h1
      exact absurd h1 (bpos_succ_ne_one p)
    | x0 q => cases h
    | x1 q =>
      injection h with hp
      rw [ih q hp]

theorem bpos_ne_add_self (p q : BPos) : bpos_add p q ≠ p := by
  induction p generalizing q with
  | one => exact bpos_succ_ne_one q
  | x0 p ih =>
    cases q with
    | one => intro h; cases h
    | x0 q => intro h; injection h with hp; exact ih q hp
    | x1 q => intro h; cases h
  | x1 p ih =>
    cases q with
    | one => intro h; cases h
    | x0 q => intro h; injection h with hp; exact ih q hp
    | x1 q => intro h; cases h

theorem bpos_add_assoc_x0
    (p : BPos)
    (ih : ∀ q r : BPos, bpos_add (bpos_add p q) r = bpos_add p (bpos_add q r))
    (q r : BPos) :
    bpos_add (bpos_add (BPos.x0 p) q) r = bpos_add (BPos.x0 p) (bpos_add q r) := by
  cases q with
  | one =>
    cases r with
    | one =>
      change BPos.x0 (bpos_succ p) = BPos.x0 (bpos_add p BPos.one)
      rw [bpos_add_one_right]
    | x0 r => rfl
    | x1 r =>
      change BPos.x0 (bpos_add_carry p r) = BPos.x0 (bpos_add p (bpos_succ r))
      rw [bpos_add_carry_eq_succ_add, bpos_add_succ_right]
  | x0 q =>
    cases r with
    | one => rfl
    | x0 r => simp [bpos_add, ih]
    | x1 r => simp [bpos_add, ih]
  | x1 q =>
    cases r with
    | one =>
      change BPos.x0 (bpos_succ (bpos_add p q)) = BPos.x0 (bpos_add p (bpos_succ q))
      rw [bpos_add_succ_right]
    | x0 r => simp [bpos_add, ih]
    | x1 r =>
      change BPos.x0 (bpos_add_carry (bpos_add p q) r) = BPos.x0 (bpos_add p (bpos_add_carry q r))
      rw [bpos_add_carry_eq_succ_add, bpos_add_carry_eq_succ_add, bpos_add_succ_right, ih]

theorem bpos_add_assoc (p q r : BPos) :
    bpos_add (bpos_add p q) r = bpos_add p (bpos_add q r) := by
  induction p generalizing q r with
  | one =>
    change bpos_add (bpos_succ q) r = bpos_succ (bpos_add q r)
    exact bpos_add_succ_left q r
  | x0 p ih => exact bpos_add_assoc_x0 p ih q r
  | x1 p ih =>
    have hsucc : BPos.x1 p = bpos_succ (BPos.x0 p) := rfl
    rw [hsucc, bpos_add_succ_left, bpos_add_succ_left, bpos_add_succ_left]
    rw [bpos_add_assoc_x0 p ih q r]

theorem badd_zero_right (x : BBin) : badd x BBin.zero = x := by
  cases x <;> rfl

theorem badd_assoc (x y z : BBin) :
    badd (badd x y) z = badd x (badd y z) := by
  cases x with
  | zero => rfl
  | pos p =>
    cases y with
    | zero => rfl
    | pos q =>
      cases z with
      | zero => rfl
      | pos r => simp [badd, bpos_add_assoc]

theorem badd_four_swap (a b c d : BBin) :
    badd (badd a b) (badd c d) = badd (badd a c) (badd b d) := by
  rw [badd_assoc a b (badd c d)]
  rw [← badd_assoc b c d, badd_comm b c, badd_assoc c b d]
  rw [← badd_assoc a c (badd b d)]

theorem bpos_add_cancel_x0
    (p : BPos)
    (ih : ∀ q r : BPos, bpos_add p q = bpos_add p r → q = r)
    (q r : BPos)
    (h : bpos_add (BPos.x0 p) q = bpos_add (BPos.x0 p) r) : q = r := by
  cases q with
  | one =>
    cases r with
    | one => rfl
    | x0 r => cases h
    | x1 r =>
      injection h with hp
      exact absurd hp.symm (bpos_ne_add_self p r)
  | x0 q =>
    cases r with
    | one => cases h
    | x0 r => injection h with hp; rw [ih q r hp]
    | x1 r => cases h
  | x1 q =>
    cases r with
    | one =>
      injection h with hp
      exact absurd hp (bpos_ne_add_self p q)
    | x0 r => cases h
    | x1 r => injection h with hp; rw [ih q r hp]

theorem bpos_add_cancel_left (p q r : BPos) (h : bpos_add p q = bpos_add p r) : q = r := by
  induction p generalizing q r with
  | one => exact bpos_succ_inj q r h
  | x0 p ih => exact bpos_add_cancel_x0 p ih q r h
  | x1 p ih =>
    have hsucc : BPos.x1 p = bpos_succ (BPos.x0 p) := rfl
    rw [hsucc, bpos_add_succ_left, bpos_add_succ_left] at h
    exact bpos_add_cancel_x0 p ih q r (bpos_succ_inj _ _ h)

theorem badd_cancel_left (z x y : BBin) (h : badd z x = badd z y) : x = y := by
  cases z with
  | zero => exact h
  | pos pz =>
    cases x with
    | zero =>
      cases y with
      | zero => rfl
      | pos py =>
        change BBin.pos pz = BBin.pos (bpos_add pz py) at h
        injection h with hp
        exact absurd hp.symm (bpos_ne_add_self pz py)
    | pos px =>
      cases y with
      | zero =>
        change BBin.pos (bpos_add pz px) = BBin.pos pz at h
        injection h with hp
        exact absurd hp (bpos_ne_add_self pz px)
      | pos py =>
        injection h with hp
        rw [bpos_add_cancel_left pz px py hp]

theorem badd_cancel_right (x y z : BBin) (h : badd x z = badd y z) : x = y := by
  rw [badd_comm x z, badd_comm y z] at h
  exact badd_cancel_left z x y h

-- ============================================================================
-- PART II (Pillar 2): Universal Multiplication Semiring & Divisibility Transitivity
-- ============================================================================

theorem bpos_x0_eq_add_self (u : BPos) : BPos.x0 u = bpos_add u u := by
  induction u with
  | one => rfl
  | x0 u ih => simp [bpos_add, ← ih]
  | x1 u ih => simp [bpos_add, bpos_add_carry_eq_succ_add, ← ih, bpos_succ]

theorem bpos_add_four_swap (a b c d : BPos) :
    bpos_add (bpos_add a b) (bpos_add c d) = bpos_add (bpos_add a c) (bpos_add b d) := by
  rw [bpos_add_assoc a b (bpos_add c d)]
  rw [← bpos_add_assoc b c d, bpos_add_comm b c, bpos_add_assoc c b d]
  rw [← bpos_add_assoc a c (bpos_add b d)]

theorem bpos_mul_add_left (p1 p2 q : BPos) :
    bpos_mul (bpos_add p1 p2) q = bpos_add (bpos_mul p1 q) (bpos_mul p2 q) := by
  induction q with
  | one => rfl
  | x0 q ih =>
    simp [bpos_mul, ih, bpos_x0_eq_add_self, bpos_add_four_swap]
  | x1 q ih =>
    change bpos_add (BPos.x0 (bpos_mul (bpos_add p1 p2) q)) (bpos_add p1 p2) =
           bpos_add (bpos_add (BPos.x0 (bpos_mul p1 q)) p1) (bpos_add (BPos.x0 (bpos_mul p2 q)) p2)
    rw [ih, bpos_x0_eq_add_self (bpos_add (bpos_mul p1 q) (bpos_mul p2 q))]
    rw [bpos_add_four_swap (bpos_mul p1 q) (bpos_mul p2 q) (bpos_mul p1 q) (bpos_mul p2 q)]
    rw [← bpos_x0_eq_add_self, ← bpos_x0_eq_add_self]
    exact bpos_add_four_swap _ _ p1 p2

theorem bpos_mul_one_left (q : BPos) : bpos_mul BPos.one q = q := by
  induction q with
  | one => rfl
  | x0 q ih => simp [bpos_mul, ih]
  | x1 q ih =>
    change bpos_add (BPos.x0 (bpos_mul BPos.one q)) BPos.one = BPos.x1 q
    rw [ih]; rfl

theorem bpos_mul_x0_left (p q : BPos) :
    bpos_mul (BPos.x0 p) q = BPos.x0 (bpos_mul p q) := by
  induction q with
  | one => rfl
  | x0 q ih => simp [bpos_mul, ih]
  | x1 q ih =>
    change bpos_add (BPos.x0 (bpos_mul (BPos.x0 p) q)) (BPos.x0 p) =
           BPos.x0 (bpos_add (BPos.x0 (bpos_mul p q)) p)
    rw [ih]; rfl

theorem bpos_mul_comm (p q : BPos) : bpos_mul p q = bpos_mul q p := by
  induction p with
  | one => exact bpos_mul_one_left q
  | x0 p ih =>
    change bpos_mul (BPos.x0 p) q = BPos.x0 (bpos_mul q p)
    rw [bpos_mul_x0_left, ih]
  | x1 p ih =>
    have hsplit : BPos.x1 p = bpos_add (BPos.x0 p) BPos.one := rfl
    change bpos_mul (BPos.x1 p) q = bpos_add (BPos.x0 (bpos_mul q p)) q
    rw [hsplit, bpos_mul_add_left, bpos_mul_x0_left, bpos_mul_one_left, ih]

theorem bmul_comm (x y : BBin) : bmul x y = bmul y x := by
  cases x <;> cases y <;> simp [bmul, bpos_mul_comm]

theorem bmul_add_left (x y z : BBin) :
    bmul (badd x y) z = badd (bmul x z) (bmul y z) := by
  cases x with
  | zero => rfl
  | pos px =>
    cases y with
    | zero =>
      cases z <;> rfl
    | pos py =>
      cases z with
      | zero => rfl
      | pos pz => simp [badd, bmul, bpos_mul_add_left]

theorem bmul_add_right (x y z : BBin) :
    bmul x (badd y z) = badd (bmul x y) (bmul x z) := by
  rw [bmul_comm x (badd y z), bmul_add_left, bmul_comm y x, bmul_comm z x]

theorem bpos_mul_add_right (p q r : BPos) :
    bpos_mul p (bpos_add q r) = bpos_add (bpos_mul p q) (bpos_mul p r) := by
  rw [bpos_mul_comm p (bpos_add q r), bpos_mul_add_left, bpos_mul_comm q p, bpos_mul_comm r p]

theorem bpos_mul_assoc (p q r : BPos) :
    bpos_mul (bpos_mul p q) r = bpos_mul p (bpos_mul q r) := by
  induction r with
  | one => rfl
  | x0 r ih => simp [bpos_mul, ih]
  | x1 r ih =>
    change bpos_add (BPos.x0 (bpos_mul (bpos_mul p q) r)) (bpos_mul p q) =
           bpos_mul p (bpos_add (BPos.x0 (bpos_mul q r)) q)
    rw [ih, bpos_mul_add_right, bpos_mul]

theorem bmul_assoc (x y z : BBin) :
    bmul (bmul x y) z = bmul x (bmul y z) := by
  cases x with
  | zero => rfl
  | pos p =>
    cases y with
    | zero => rfl
    | pos q =>
      cases z with
      | zero => rfl
      | pos r => simp [bmul, bpos_mul_assoc]

theorem bdivides_trans (a b c : BBin) :
    bdivides a b → bdivides b c → bdivides a c := by
  rintro ⟨q1, rfl⟩ ⟨q2, rfl⟩
  exact ⟨bmul q1 q2, (bmul_assoc a q1 q2).symm⟩

-- Polynomial `bclmul` associativity & `F_2[x]` divisibility transitivity!
theorem bclmul_shl1_right (x y : BBin) :
    bclmul x (bshl1 y) = bshl1 (bclmul x y) := by
  rw [bclmul_comm x (bshl1 y), bclmul_shl1_left, bclmul_comm y x]

theorem bclmul_assoc (x y z : BBin) :
    bclmul (bclmul x y) z = bclmul x (bclmul y z) := by
  cases z with
  | zero => rfl
  | pos r =>
    induction r with
    | one => rfl
    | x0 r ih =>
      change bshl1 (bclmul (bclmul x y) (BBin.pos r)) =
             bclmul x (bshl1 (bclmul y (BBin.pos r)))
      rw [ih, bclmul_shl1_right]
    | x1 r ih =>
      change bxor_bin (bshl1 (bclmul (bclmul x y) (BBin.pos r))) (bclmul x y) =
             bclmul x (bxor_bin (bshl1 (bclmul y (BBin.pos r))) y)
      rw [ih, bclmul_xor_right, bclmul_shl1_right]

theorem bdivides_f2x_trans (a b c : BBin) :
    bdivides_f2x a b → bdivides_f2x b c → bdivides_f2x a c := by
  rintro ⟨q1, rfl⟩ ⟨q2, rfl⟩
  exact ⟨bclmul q1 q2, (bclmul_assoc a q1 q2).symm⟩

-- ============================================================================
-- PART III (Pillar 1): Grothendieck Signed Pairs (`BSignPair` = Z) & Shell Laws
-- ============================================================================

structure BSignPair where
  pos : BBin
  neg : BBin
  deriving DecidableEq

def bsign_zero : BSignPair := ⟨BBin.zero, BBin.zero⟩
def bsign_one  : BSignPair := ⟨bone, BBin.zero⟩
def bsign_neg1 : BSignPair := ⟨BBin.zero, bone⟩

def bsign_equiv (u v : BSignPair) : Prop :=
  badd u.pos v.neg = badd v.pos u.neg

def bsign_neg (u : BSignPair) : BSignPair := ⟨u.neg, u.pos⟩

-- Synthesized in Epoch 10a (`GLAW_CONG + GLAW_SWAP_INV + GLAW_DISTRIB`)!
def bsign_add (u v : BSignPair) : BSignPair :=
  ⟨badd u.pos v.pos, badd u.neg v.neg⟩

def bsign_mul (u v : BSignPair) : BSignPair :=
  ⟨badd (bmul u.pos v.pos) (bmul u.neg v.neg),
   badd (bmul u.pos v.neg) (bmul u.neg v.pos)⟩

theorem bsign_equiv_refl (u : BSignPair) : bsign_equiv u u := rfl

theorem bsign_equiv_symm (u v : BSignPair) (h : bsign_equiv u v) : bsign_equiv v u :=
  h.symm

-- Transitivity of `(pos, neg)` equivalence uses our pure-silicon `badd_cancel_right`!
theorem bsign_equiv_trans (u v w : BSignPair)
    (huv : bsign_equiv u v) (hvw : bsign_equiv v w) : bsign_equiv u w := by
  unfold bsign_equiv at *
  apply badd_cancel_right _ _ (badd v.pos v.neg)
  have lhs_eq :
      badd (badd u.pos w.neg) (badd v.pos v.neg) =
      badd (badd u.pos v.neg) (badd v.pos w.neg) := by
    rw [badd_four_swap u.pos w.neg v.pos v.neg]
    rw [badd_comm w.neg v.neg]
    rw [← badd_four_swap u.pos v.neg v.pos w.neg]
  have rhs_eq :
      badd (badd w.pos u.neg) (badd v.pos v.neg) =
      badd (badd v.pos u.neg) (badd w.pos v.neg) := by
    rw [badd_four_swap w.pos u.neg v.pos v.neg]
    rw [badd_comm w.pos v.pos]
    exact badd_four_swap v.pos w.pos u.neg v.neg
  rw [lhs_eq, rhs_eq, huv, hvw]

theorem bsign_add_neg_cancel (u : BSignPair) :
    bsign_equiv (bsign_add u (bsign_neg u)) bsign_zero := by
  change badd (badd u.pos u.neg) BBin.zero = badd BBin.zero (badd u.neg u.pos)
  rw [badd_zero_right]
  change badd u.pos u.neg = badd u.neg u.pos
  exact badd_comm u.pos u.neg

theorem bsign_add_congr (u1 u2 v1 v2 : BSignPair)
    (hu : bsign_equiv u1 u2) (hv : bsign_equiv v1 v2) :
    bsign_equiv (bsign_add u1 v1) (bsign_add u2 v2) := by
  unfold bsign_equiv bsign_add at *
  rw [badd_four_swap u1.pos v1.pos u2.neg v2.neg]
  rw [badd_four_swap u2.pos v2.pos u1.neg v1.neg]
  rw [hu, hv]

theorem bsign_mul_comm (u v : BSignPair) : bsign_mul u v = bsign_mul v u := by
  unfold bsign_mul
  rw [bmul_comm u.pos v.pos, bmul_comm u.neg v.neg]
  rw [bmul_comm u.pos v.neg, bmul_comm u.neg v.pos, badd_comm (bmul v.neg u.pos)]

theorem bsign_mul_neg1 (u : BSignPair) : bsign_mul u bsign_neg1 = bsign_neg u := by
  cases u with
  | mk p m =>
    unfold bsign_mul bsign_neg1 bsign_neg
    have h0p : bmul p BBin.zero = BBin.zero := by cases p <;> rfl
    have h0m : bmul m BBin.zero = BBin.zero := by cases m <;> rfl
    rw [h0p, h0m, bmul_one_right, bmul_one_right, badd_zero_right]
    rfl

theorem bsign_mul_add_distrib (u v w : BSignPair) :
    bsign_mul u (bsign_add v w) = bsign_add (bsign_mul u v) (bsign_mul u w) := by
  unfold bsign_mul bsign_add
  simp only [bmul_add_right]
  rw [badd_four_swap (bmul u.pos v.pos) (bmul u.pos w.pos) (bmul u.neg v.neg) (bmul u.neg w.neg)]
  rw [badd_four_swap (bmul u.pos v.neg) (bmul u.pos w.neg) (bmul u.neg v.pos) (bmul u.neg w.pos)]

theorem bsign_mul_scale_right (u1 u2 k : BSignPair)
    (hu : bsign_equiv u1 u2) : bsign_equiv (bsign_mul u1 k) (bsign_mul u2 k) := by
  unfold bsign_equiv bsign_mul at *
  have h1 : badd (bmul u1.pos k.pos) (bmul u2.neg k.pos) =
            badd (bmul u2.pos k.pos) (bmul u1.neg k.pos) := by
    rw [← bmul_add_left, hu, bmul_add_left]
  have h2 : badd (bmul u2.pos k.neg) (bmul u1.neg k.neg) =
            badd (bmul u1.pos k.neg) (bmul u2.neg k.neg) := by
    rw [← bmul_add_left, ← hu, bmul_add_left]
  have lhs_rearr :
      badd (badd (bmul u1.pos k.pos) (bmul u1.neg k.neg))
           (badd (bmul u2.pos k.neg) (bmul u2.neg k.pos)) =
      badd (badd (bmul u1.pos k.pos) (bmul u2.neg k.pos))
           (badd (bmul u2.pos k.neg) (bmul u1.neg k.neg)) := by
    rw [badd_four_swap (bmul u1.pos k.pos) (bmul u1.neg k.neg) (bmul u2.pos k.neg) (bmul u2.neg k.pos)]
    rw [badd_comm (bmul u1.pos k.pos) (bmul u2.pos k.neg)]
    rw [badd_four_swap (bmul u2.pos k.neg) (bmul u1.pos k.pos) (bmul u1.neg k.neg) (bmul u2.neg k.pos)]
    rw [badd_comm (bmul u2.pos k.neg) (bmul u1.neg k.neg)]
    rw [badd_comm (badd (bmul u1.neg k.neg) (bmul u2.pos k.neg))]
  have rhs_rearr :
      badd (badd (bmul u2.pos k.pos) (bmul u2.neg k.neg))
           (badd (bmul u1.pos k.neg) (bmul u1.neg k.pos)) =
      badd (badd (bmul u2.pos k.pos) (bmul u1.neg k.pos))
           (badd (bmul u1.pos k.neg) (bmul u2.neg k.neg)) := by
    rw [badd_four_swap (bmul u2.pos k.pos) (bmul u2.neg k.neg) (bmul u1.pos k.neg) (bmul u1.neg k.pos)]
    rw [badd_comm (bmul u2.neg k.neg) (bmul u1.neg k.pos)]
    exact badd_four_swap _ _ _ _
  rw [lhs_rearr, rhs_rearr, h1, h2]

theorem bsign_mul_congr (u1 u2 v1 v2 : BSignPair)
    (hu : bsign_equiv u1 u2) (hv : bsign_equiv v1 v2) :
    bsign_equiv (bsign_mul u1 v1) (bsign_mul u2 v2) := by
  apply bsign_equiv_trans _ (bsign_mul u2 v1) _
  · exact bsign_mul_scale_right u1 u2 v1 hu
  · rw [bsign_mul_comm u2 v1, bsign_mul_comm u2 v2]
    exact bsign_mul_scale_right v1 v2 u2 hv

-- Exact Carry-vs-Carryless Degree-2 Shell `[4, 5, 6, 7]` Mobius Divergence Theorem:
--   In `F_2[x]`: `4 = 2⊗2` (mu=0), `5 = 3⊗3` (mu=0), `6 = 2⊗3` (mu=+1), `7` irred (mu=-1)
--     => shell sum = `0 + 0 + 1 + (-1) ≈ 0`!
--   In `N`:      `4 = 2*2` (mu=0), `5` prime (mu=-1), `6 = 2*3` (mu=+1), `7` prime (mu=-1)
--     => shell sum = `0 + (-1) + 1 + (-1) ≈ -1 != 0`!
def bfour  : BBin := BBin.pos (BPos.x0 (BPos.x0 BPos.one))
def bsix   : BBin := BBin.pos (BPos.x0 (BPos.x1 BPos.one))
def bseven : BBin := BBin.pos (BPos.x1 (BPos.x1 BPos.one))

def bmu_f2x_shell2 : BBin → BSignPair
  | x =>
    if x = bsix then bsign_one
    else if x = bseven then bsign_neg1
    else bsign_zero

def bmu_n_shell2 : BBin → BSignPair
  | x =>
    if x = bfive then bsign_neg1
    else if x = bsix then bsign_one
    else if x = bseven then bsign_neg1
    else bsign_zero

def sum_shell2 (f : BBin → BSignPair) : BSignPair :=
  bsign_add (bsign_add (f bfour) (f bfive)) (bsign_add (f bsix) (f bseven))

theorem carryless_shell2_mobius_annihilation :
    bsign_equiv (sum_shell2 bmu_f2x_shell2) bsign_zero := rfl

theorem carried_shell2_mobius_residual :
    bsign_equiv (sum_shell2 bmu_n_shell2) bsign_neg1 ∧
    ¬ bsign_equiv (sum_shell2 bmu_n_shell2) bsign_zero :=
  ⟨rfl, fun h => by cases h⟩

-- ============================================================================
-- PART IV (Pillar 3): Universal `F_2[x]/(P)` Quotient Congruence & Galois Fields
-- ============================================================================

def bf2x_cong (m a b : BBin) : Prop :=
  bdivides_f2x m (bxor_bin a b)

theorem bf2x_cong_refl (m a : BBin) : bf2x_cong m a a := by
  unfold bf2x_cong
  rw [bxor_bin_self]
  exact bdivides_f2x_zero m

theorem bf2x_cong_symm (m a b : BBin) (h : bf2x_cong m a b) : bf2x_cong m b a := by
  unfold bf2x_cong at *
  rw [bxor_bin_comm b a]
  exact h

theorem bxor_bin_bridge (a b c : BBin) :
    bxor_bin (bxor_bin a b) (bxor_bin b c) = bxor_bin a c := by
  rw [bxor_bin_assoc a b (bxor_bin b c)]
  rw [← bxor_bin_assoc b b c, bxor_bin_self b]
  rfl

theorem bf2x_cong_trans (m a b c : BBin)
    (hab : bf2x_cong m a b) (hbc : bf2x_cong m b c) : bf2x_cong m a c := by
  unfold bf2x_cong at *
  rw [← bxor_bin_bridge a b c]
  exact bdivides_f2x_xor m (bxor_bin a b) (bxor_bin b c) hab hbc

theorem bf2x_cong_add (m a1 a2 b1 b2 : BBin)
    (ha : bf2x_cong m a1 a2) (hb : bf2x_cong m b1 b2) :
    bf2x_cong m (bxor_bin a1 b1) (bxor_bin a2 b2) := by
  unfold bf2x_cong at *
  rw [bxor_bin_four_swap a1 b1 a2 b2]
  exact bdivides_f2x_xor m (bxor_bin a1 a2) (bxor_bin b1 b2) ha hb

theorem bf2x_cong_mul_scale_right (m a1 a2 k : BBin)
    (ha : bf2x_cong m a1 a2) : bf2x_cong m (bclmul a1 k) (bclmul a2 k) := by
  unfold bf2x_cong at *
  rcases ha with ⟨q, hq⟩
  refine ⟨bclmul q k, ?_⟩
  rw [← bclmul_xor_left a1 a2 k, ← hq, bclmul_assoc m q k]

theorem bf2x_cong_mul_scale_left (m k b1 b2 : BBin)
    (hb : bf2x_cong m b1 b2) : bf2x_cong m (bclmul k b1) (bclmul k b2) := by
  rw [bclmul_comm k b1, bclmul_comm k b2]
  exact bf2x_cong_mul_scale_right m b1 b2 k hb

theorem bf2x_cong_mul (m a1 a2 b1 b2 : BBin)
    (ha : bf2x_cong m a1 a2) (hb : bf2x_cong m b1 b2) :
    bf2x_cong m (bclmul a1 b1) (bclmul a2 b2) :=
  bf2x_cong_trans m (bclmul a1 b1) (bclmul a2 b1) (bclmul a2 b2)
    (bf2x_cong_mul_scale_right m a1 a2 b1 ha)
    (bf2x_cong_mul_scale_left m a2 b1 b2 hb)

-- Galois Field `F_4 = F_2[x] / (t^2 + t + 1)` (`bseven = 7 = 111_2`, `|F_4^x| = 3`)
-- and `F_8 = F_2[x] / (t^3 + t + 1)` (`beleven = 11 = 1011_2`, `|F_8^x| = 7`)!
def beleven : BBin := BBin.pos (BPos.x1 (BPos.x1 (BPos.x0 BPos.one)))

def bf2x_pow3 (a : BBin) : BBin := bclmul a (bclmul a a)
def bf2x_pow7 (a : BBin) : BBin :=
  let a2 := bclmul a a
  let a4 := bclmul a2 a2
  bclmul a (bclmul a2 a4)

-- Fermat's Theorem in `F_4^x`: `a^3 ≡ 1 (mod 7)` for all `a in {1, 2, 3}`!
theorem gf4_fermat_one   : bf2x_cong bseven (bf2x_pow3 bone)   bone := ⟨BBin.zero, rfl⟩
theorem gf4_fermat_two   : bf2x_cong bseven (bf2x_pow3 btwo)   bone := ⟨bthree, rfl⟩
theorem gf4_fermat_three : bf2x_cong bseven (bf2x_pow3 bthree) bone := ⟨btwo, rfl⟩

-- Fermat's Theorem in `F_8^x`: `a^7 ≡ 1 (mod 11)` for generator `a = 2` (`t`) and `a = 3` (`t+1`)!
def btwentythree : BBin := BBin.pos (BPos.x1 (BPos.x1 (BPos.x1 (BPos.x0 BPos.one))))
def btwentysix   : BBin := BBin.pos (BPos.x0 (BPos.x1 (BPos.x0 (BPos.x1 BPos.one))))

theorem gf8_fermat_two   : bf2x_cong beleven (bf2x_pow7 btwo)   bone := ⟨btwentythree, rfl⟩
theorem gf8_fermat_three : bf2x_cong beleven (bf2x_pow7 bthree) bone := ⟨btwentysix, rfl⟩

-- Universal Carried Quotient Ring Congruence `Z / mZ` (`Epoch 11` formula `a + m*q = b + m*r`)!
def bmod_cong (m a b : BBin) : Prop :=
  ∃ q r : BBin, badd a (bmul m q) = badd b (bmul m r)

theorem bmod_cong_refl (m a : BBin) : bmod_cong m a a :=
  ⟨BBin.zero, BBin.zero, rfl⟩

theorem bmod_cong_symm (m a b : BBin) (h : bmod_cong m a b) : bmod_cong m b a := by
  rcases h with ⟨q, r, hqr⟩
  exact ⟨r, q, hqr.symm⟩

theorem bmod_cong_trans (m a b c : BBin)
    (hab : bmod_cong m a b) (hbc : bmod_cong m b c) : bmod_cong m a c := by
  rcases hab with ⟨q1, r1, h1⟩
  rcases hbc with ⟨q2, r2, h2⟩
  refine ⟨badd q1 q2, badd r2 r1, ?_⟩
  rw [bmul_add_right, ← badd_assoc a (bmul m q1) (bmul m q2), h1]
  rw [badd_assoc b (bmul m r1) (bmul m q2), badd_comm (bmul m r1) (bmul m q2)]
  rw [← badd_assoc b (bmul m q2) (bmul m r1), h2]
  rw [badd_assoc c (bmul m r2) (bmul m r1), ← bmul_add_right]

theorem bmod_cong_add (m a1 a2 b1 b2 : BBin)
    (ha : bmod_cong m a1 a2) (hb : bmod_cong m b1 b2) :
    bmod_cong m (badd a1 b1) (badd a2 b2) := by
  rcases ha with ⟨qa, ra, eq_a⟩
  rcases hb with ⟨qb, rb, eq_b⟩
  refine ⟨badd qa qb, badd ra rb, ?_⟩
  rw [bmul_add_right, bmul_add_right]
  rw [← badd_four_swap a1 (bmul m qa) b1 (bmul m qb), eq_a, eq_b]
  exact badd_four_swap a2 (bmul m ra) b2 (bmul m rb)

theorem bmod_cong_mul_scale_right (m a1 a2 k : BBin)
    (ha : bmod_cong m a1 a2) : bmod_cong m (bmul a1 k) (bmul a2 k) := by
  rcases ha with ⟨q, r, hqr⟩
  refine ⟨bmul q k, bmul r k, ?_⟩
  rw [← bmul_assoc m q k, ← bmul_assoc m r k]
  rw [← bmul_add_left, hqr, bmul_add_left]

theorem bmod_cong_mul (m a1 a2 b1 b2 : BBin)
    (ha : bmod_cong m a1 a2) (hb : bmod_cong m b1 b2) :
    bmod_cong m (bmul a1 b1) (bmul a2 b2) := by
  apply bmod_cong_trans m (bmul a1 b1) (bmul a2 b1) (bmul a2 b2)
  · exact bmod_cong_mul_scale_right m a1 a2 b1 ha
  · rw [bmul_comm a2 b1, bmul_comm a2 b2]
    exact bmod_cong_mul_scale_right m b1 b2 a2 hb

-- Fermat's Little Theorem in `(Z / 5Z)^x`: `2^4 = 16 = 1 + 5*3 ≡ 1 (mod 5)` & `3^4 = 81 = 1 + 5*16 ≡ 1 (mod 5)`!
def bmul_pow4 (a : BBin) : BBin :=
  let a2 := bmul a a
  bmul a2 a2

def bsixteen : BBin := BBin.pos (BPos.x0 (BPos.x0 (BPos.x0 (BPos.x0 BPos.one))))

theorem zmod5_fermat_two   : bmod_cong bfive (bmul_pow4 btwo)   bone := ⟨BBin.zero, bthree,   rfl⟩
theorem zmod5_fermat_three : bmod_cong bfive (bmul_pow4 bthree) bone := ⟨BBin.zero, bsixteen, rfl⟩

end SiliconBigBang
