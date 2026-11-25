/-
  Pure-Silicon Mathematical "Big Bang" — Track 1 Zero-Dependency Lean 4 Kernel Proofs
  (`lean/Track1UnshackledVerify.lean`: Epochs 41..44 Unshackled Discovery Engine)

  NO Mathlib. NO built-in `Nat`, `Int`, `Rat`, `Real`, or `Bool` arithmetic used anywhere.
  Verifies the discoveries of `track1_unshackled_miner.hip` strictly from Epoch-0 `BBit`,
  `BPos`, `BBin`, and `BSignPair`:
    1. Sharp Pareto-Tight Hasse Frontier Inequality discovered blindly on GPU:
       `bpopcnt_add_le_or`: `∀ x y : BBin, popcnt(x + y) <= popcnt(x | y)`!
    2. Universal Carry-Less Bounded By Carried Multiplication:
       `bclmul_le_bmul`: `∀ x y : BBin, clmul(x, y) <= x * y`, plus disjoint carry-free
       collapse `band_bin x y = 0 -> badd x y = bxor_bin x y`.
    3. Multi-State `mod 3` Binary DFA Soundness (`mod3_pos_succ`) & Stern-Brocot /
       Calkin-Wilf Common-Divisor Shear Invariance (`bsign_dvd_stern_shear_iff`).
    4. 140 Auto-Compiled Rescued Epoch-6 Positive-Domain Conditional Theorems
       (`auto_rescued_cond_e6_0 .. auto_rescued_cond_e6_139`).
-/

import BitCircuitSynthesis.BigBangScratchVerify
import BitCircuitSynthesis.Epoch7PrimesVerify
import BitCircuitSynthesis.Epoch10AllThreeVerify
import BitCircuitSynthesis.AutoCompiledArenaVerify

namespace SiliconBigBang

-- ============================================================================
-- PART I: Sharp Hasse Frontier Theorem `popcnt(x + y) <= popcnt(x | y)`
-- ============================================================================

def bpos_or : BPos → BPos → BPos
  | BPos.one,  BPos.one  => BPos.one
  | BPos.one,  BPos.x0 q => BPos.x1 q
  | BPos.one,  BPos.x1 q => BPos.x1 q
  | BPos.x0 p, BPos.one  => BPos.x1 p
  | BPos.x1 p, BPos.one  => BPos.x1 p
  | BPos.x0 p, BPos.x0 q => BPos.x0 (bpos_or p q)
  | BPos.x0 p, BPos.x1 q => BPos.x1 (bpos_or p q)
  | BPos.x1 p, BPos.x0 q => BPos.x1 (bpos_or p q)
  | BPos.x1 p, BPos.x1 q => BPos.x1 (bpos_or p q)

def bor_bin : BBin → BBin → BBin
  | BBin.zero, y => y
  | x, BBin.zero => x
  | BBin.pos p, BBin.pos q => BBin.pos (bpos_or p q)

def bpos_popcnt : BPos → BPos
  | BPos.one  => BPos.one
  | BPos.x0 p => bpos_popcnt p
  | BPos.x1 p => bpos_succ (bpos_popcnt p)

def bpopcnt : BBin → BBin
  | BBin.zero  => BBin.zero
  | BBin.pos p => BBin.pos (bpos_popcnt p)

theorem bsucc_eq_add_one (x : BBin) : bsucc x = badd x bone := by
  cases x with
  | zero => rfl
  | pos p =>
    change BBin.pos (bpos_succ p) = BBin.pos (bpos_add p BPos.one)
    rw [bpos_add_one_right]

theorem ble_alg_zero_left (x : BBin) : ble_alg BBin.zero x :=
  ⟨x, rfl⟩

theorem ble_alg_trans {a b c : BBin} (hab : ble_alg a b) (hbc : ble_alg b c) :
    ble_alg a c := by
  rcases hab with ⟨w1, hw1⟩
  rcases hbc with ⟨w2, hw2⟩
  refine ⟨badd w1 w2, ?_⟩
  rw [← badd_assoc, hw1, hw2]

theorem ble_alg_succ_right {a b : BBin} (h : ble_alg a b) :
    ble_alg a (bsucc b) := by
  refine ble_alg_trans h ⟨bone, ?_⟩
  exact (bsucc_eq_add_one b).symm

theorem ble_alg_succ_mono {a b : BBin} (h : ble_alg a b) :
    ble_alg (bsucc a) (bsucc b) := by
  rcases h with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  rw [bsucc_eq_add_one a, bsucc_eq_add_one b, ← hw]
  rw [badd_assoc a bone w, badd_comm bone w, ← badd_assoc a w bone]

theorem ble_alg_add_mono {a1 b1 a2 b2 : BBin}
    (h1 : ble_alg a1 b1) (h2 : ble_alg a2 b2) :
    ble_alg (badd a1 a2) (badd b1 b2) := by
  rcases h1 with ⟨w1, hw1⟩
  rcases h2 with ⟨w2, hw2⟩
  refine ⟨badd w1 w2, ?_⟩
  rw [← hw1, ← hw2]
  -- `(a1 + a2) + (w1 + w2) = (a1 + w1) + (a2 + w2)`
  rw [badd_assoc a1 a2 (badd w1 w2)]
  rw [← badd_assoc a2 w1 w2, badd_comm a2 w1, badd_assoc w1 a2 w2]
  rw [← badd_assoc a1 w1 (badd a2 w2)]

-- Key 1-Variable Carry-Absorption Lemma: `popcnt(succ p) <= popcnt(p) + 1`!
theorem bpos_popcnt_succ_le (p : BPos) :
    ble_alg (BBin.pos (bpos_popcnt (bpos_succ p))) (bsucc (BBin.pos (bpos_popcnt p))) := by
  induction p with
  | one =>
    exact ⟨bone, rfl⟩
  | x0 p _ =>
    exact ble_alg_refl _
  | x1 p ih =>
    change ble_alg (BBin.pos (bpos_popcnt (bpos_succ p))) (bsucc (bsucc (BBin.pos (bpos_popcnt p))))
    exact ble_alg_succ_right ih

theorem bpos_popcnt_add_le_or (p q : BPos) :
    ble_alg (BBin.pos (bpos_popcnt (bpos_add p q))) (BBin.pos (bpos_popcnt (bpos_or p q))) := by
  induction p generalizing q with
  | one =>
    cases q with
    | one  => exact ble_alg_refl _
    | x0 q => exact ble_alg_refl _
    | x1 q =>
      change ble_alg (BBin.pos (bpos_popcnt (bpos_succ q))) (bsucc (BBin.pos (bpos_popcnt q)))
      exact bpos_popcnt_succ_le q
  | x0 p ih =>
    cases q with
    | one  => exact ble_alg_refl _
    | x0 q => exact ih q
    | x1 q =>
      change ble_alg (bsucc (BBin.pos (bpos_popcnt (bpos_add p q)))) (bsucc (BBin.pos (bpos_popcnt (bpos_or p q))))
      exact ble_alg_succ_mono (ih q)
  | x1 p ih =>
    cases q with
    | one =>
      change ble_alg (BBin.pos (bpos_popcnt (bpos_succ p))) (bsucc (BBin.pos (bpos_popcnt p)))
      exact bpos_popcnt_succ_le p
    | x0 q =>
      change ble_alg (bsucc (BBin.pos (bpos_popcnt (bpos_add p q)))) (bsucc (BBin.pos (bpos_popcnt (bpos_or p q))))
      exact ble_alg_succ_mono (ih q)
    | x1 q =>
      change ble_alg (BBin.pos (bpos_popcnt (bpos_add_carry p q))) (bsucc (BBin.pos (bpos_popcnt (bpos_or p q))))
      rw [bpos_add_carry_eq_succ_add]
      exact ble_alg_trans (bpos_popcnt_succ_le (bpos_add p q)) (ble_alg_succ_mono (ih q))

theorem bpopcnt_add_le_or (x y : BBin) :
    ble_alg (bpopcnt (badd x y)) (bpopcnt (bor_bin x y)) := by
  cases x with
  | zero =>
    cases y <;> exact ble_alg_refl _
  | pos p =>
    cases y with
    | zero => exact ble_alg_refl _
    | pos q => exact bpos_popcnt_add_le_or p q

-- ============================================================================
-- PART II: Universal `bclmul x y <= bmul x y` & Disjoint Carry-Free Collapse
-- ============================================================================

theorem bxor_le_badd (x y : BBin) : ble_alg (bxor_bin x y) (badd x y) :=
  ⟨bshl1 (band_bin x y), (bbin_carry_bridge x y).symm⟩

theorem bdisjoint_badd_eq_bxor (x y : BBin) (h : band_bin x y = BBin.zero) :
    badd x y = bxor_bin x y := by
  rw [bbin_carry_bridge x y, h]
  exact badd_zero_right (bxor_bin x y)

theorem bshl1_eq_add_dup (z : BBin) : bshl1 z = badd z z := by
  cases z with
  | zero => rfl
  | pos p =>
    have hdup : ∀ r : BPos, BPos.x0 r = bpos_add r r := by
      intro r
      induction r with
      | one => rfl
      | x0 r ih => simp [bpos_add, ← ih]
      | x1 r ih => simp [bpos_add, bpos_add_carry_eq_succ_add, ← ih, bpos_succ]
    exact congrArg BBin.pos (hdup p)

theorem ble_alg_bshl1 {a b : BBin} (h : ble_alg a b) :
    ble_alg (bshl1 a) (bshl1 b) := by
  rw [bshl1_eq_add_dup a, bshl1_eq_add_dup b]
  exact ble_alg_add_mono h h

theorem bpos_clmul_le_bmul (p q : BPos) :
    ble_alg (bpos_clmul (BBin.pos p) q) (BBin.pos (bpos_mul p q)) := by
  induction q with
  | one =>
    exact ble_alg_refl (BBin.pos p)
  | x0 q ih =>
    change ble_alg (bshl1 (bpos_clmul (BBin.pos p) q)) (bshl1 (BBin.pos (bpos_mul p q)))
    exact ble_alg_bshl1 ih
  | x1 q ih =>
    change ble_alg
      (bxor_bin (bshl1 (bpos_clmul (BBin.pos p) q)) (BBin.pos p))
      (badd (bshl1 (BBin.pos (bpos_mul p q))) (BBin.pos p))
    exact ble_alg_trans
      (bxor_le_badd (bshl1 (bpos_clmul (BBin.pos p) q)) (BBin.pos p))
      (ble_alg_add_mono (ble_alg_bshl1 ih) (ble_alg_refl (BBin.pos p)))

theorem bpos_clmul_zero (q : BPos) : bpos_clmul BBin.zero q = BBin.zero := by
  induction q with
  | one => rfl
  | x0 q ih => simp [bpos_clmul, ih, bshl1, bsnoc]
  | x1 q ih => simp [bpos_clmul, ih, bshl1, bsnoc, bxor_bin]

theorem bclmul_le_bmul (x y : BBin) : ble_alg (bclmul x y) (bmul x y) := by
  cases y with
  | zero => exact ble_alg_zero_left (bmul x BBin.zero)
  | pos q =>
    cases x with
    | zero =>
      change ble_alg (bpos_clmul BBin.zero q) BBin.zero
      rw [bpos_clmul_zero q]
      exact ble_alg_refl BBin.zero
    | pos p => exact bpos_clmul_le_bmul p q

-- ============================================================================
-- PART III: 4-State `mod 3` Binary DFA Soundness & Stern-Brocot Shear Law
-- ============================================================================

inductive Mod3State : Type where
  | r0 : Mod3State
  | r1 : Mod3State
  | r2 : Mod3State
  deriving DecidableEq

def mod3_succ : Mod3State → Mod3State
  | Mod3State.r0 => Mod3State.r1
  | Mod3State.r1 => Mod3State.r2
  | Mod3State.r2 => Mod3State.r0

def mod3_step : Mod3State → BBit → Mod3State
  | Mod3State.r0, BBit.b0 => Mod3State.r0
  | Mod3State.r0, BBit.b1 => Mod3State.r1
  | Mod3State.r1, BBit.b0 => Mod3State.r2
  | Mod3State.r1, BBit.b1 => Mod3State.r0
  | Mod3State.r2, BBit.b0 => Mod3State.r1
  | Mod3State.r2, BBit.b1 => Mod3State.r2

def mod3_pos : BPos → Mod3State
  | BPos.one  => Mod3State.r1
  | BPos.x0 p => mod3_step (mod3_pos p) BBit.b0
  | BPos.x1 p => mod3_step (mod3_pos p) BBit.b1

-- Proves universally across unbounded bit-length `BPos` that the GPU-discovered
-- `mod 3` binary DFA transitions match exact successor residue cycling `r0 -> r1 -> r2 -> r0`!
theorem mod3_pos_succ (p : BPos) :
    mod3_pos (bpos_succ p) = mod3_succ (mod3_pos p) := by
  induction p with
  | one => rfl
  | x0 p _ =>
    unfold bpos_succ mod3_pos
    cases mod3_pos p <;> rfl
  | x1 p ih =>
    unfold bpos_succ mod3_pos
    rw [ih]
    cases mod3_pos p <;> rfl

-- Exact divisibility over `BSignPair` (`Z`) and Stern-Brocot / Calkin-Wilf shear invariance:
def bsign_dvd (d a : BSignPair) : Prop :=
  ∃ k : BSignPair, bsign_equiv (bsign_mul d k) a

theorem bsign_mul_distrib_left_local (d x y : BSignPair) :
    bsign_equiv (bsign_mul d (bsign_add x y)) (bsign_add (bsign_mul d x) (bsign_mul d y)) := by
  rcases d with ⟨dp, dn⟩
  rcases x with ⟨xp, xn⟩
  rcases y with ⟨yp, yn⟩
  unfold bsign_mul bsign_add bsign_equiv
  -- Check both sides expand via `bmul_add_right` + `badd` rearrangement!
  simp only [bmul_add_right]
  -- LHS: `((dp*xp + dp*yp) + (dn*xn + dn*yn)) + ((dp*xn + dn*xp) + (dp*yn + dn*yp))`
  -- RHS: `((dp*xp + dn*xn) + (dp*yp + dn*yn)) + ((dp*xn + dp*yn) + (dn*xp + dn*yp))`
  have swap4 (a b c e : BBin) : badd (badd a b) (badd c e) = badd (badd a c) (badd b e) := by
    rw [badd_assoc a b (badd c e), ← badd_assoc b c e, badd_comm b c, badd_assoc c b e, ← badd_assoc a c (badd b e)]
  rw [swap4 (bmul dp xp) (bmul dp yp) (bmul dn xn) (bmul dn yn)]
  rw [swap4 (bmul dp xn) (bmul dn xp) (bmul dp yn) (bmul dn yp)]

theorem bsign_add_neg_right_cancel (u v : BSignPair) :
    bsign_equiv (bsign_add (bsign_add u v) (bsign_neg v)) u := by
  have h1 : bsign_equiv (bsign_add (bsign_add u v) (bsign_neg v)) (bsign_add u (bsign_add v (bsign_neg v))) := by
    rcases u with ⟨up, un⟩; rcases v with ⟨vp, vn⟩
    unfold bsign_add bsign_neg bsign_equiv
    rw [badd_assoc up vp vn, badd_assoc un vn vp]
  have h2 : bsign_equiv (bsign_add u (bsign_add v (bsign_neg v))) (bsign_add u (BSignPair.mk BBin.zero BBin.zero)) :=
    bsign_add_congr _ _ _ _ (bsign_equiv_refl u) (bsign_add_neg_cancel v)
  have h3 : bsign_equiv (bsign_add u (BSignPair.mk BBin.zero BBin.zero)) u := by
    rcases u with ⟨up, un⟩
    unfold bsign_add bsign_equiv
    rw [badd_zero_right, badd_zero_right]
  exact bsign_equiv_trans _ _ _ h1 (bsign_equiv_trans _ _ _ h2 h3)

theorem bsign_dvd_add {d u v : BSignPair} (hu : bsign_dvd d u) (hv : bsign_dvd d v) :
    bsign_dvd d (bsign_add u v) := by
  rcases hu with ⟨ku, hku⟩
  rcases hv with ⟨kv, hkv⟩
  refine ⟨bsign_add ku kv, ?_⟩
  exact bsign_equiv_trans _ _ _ (bsign_mul_distrib_left_local d ku kv) (bsign_add_congr _ _ _ _ hku hkv)

theorem bsign_dvd_neg {d v : BSignPair} (hv : bsign_dvd d v) :
    bsign_dvd d (bsign_neg v) := by
  rcases hv with ⟨k, hk⟩
  refine ⟨bsign_neg k, ?_⟩
  have hneg : bsign_mul d (bsign_neg k) = bsign_neg (bsign_mul d k) := by
    rcases d with ⟨dp, dn⟩; rcases k with ⟨kp, kn⟩
    unfold bsign_mul bsign_neg
    rw [badd_comm (bmul dp kn) (bmul dn kp), badd_comm (bmul dp kp) (bmul dn kn)]
  rw [hneg]
  rcases h_mk : bsign_mul d k with ⟨mp, mn⟩
  rcases v with ⟨vp, vn⟩
  rw [h_mk] at hk
  unfold bsign_neg bsign_equiv at *
  rw [badd_comm mn vp, badd_comm vn mp]
  exact hk.symm

-- Stern-Brocot / Calkin-Wilf Additive Shear Divisibility Biconditional:
-- `d | u ∧ d | v  <->  d | (u + v) ∧ d | v`!
theorem bsign_dvd_stern_shear_iff (d u v : BSignPair) :
    (bsign_dvd d u ∧ bsign_dvd d v) ↔ (bsign_dvd d (bsign_add u v) ∧ bsign_dvd d v) := by
  constructor
  · rintro ⟨hu, hv⟩
    exact ⟨bsign_dvd_add hu hv, hv⟩
  · rintro ⟨huv, hv⟩
    refine ⟨?_, hv⟩
    rcases bsign_dvd_add huv (bsign_dvd_neg hv) with ⟨k, hk⟩
    exact ⟨k, bsign_equiv_trans _ _ _ hk (bsign_add_neg_right_cancel u v)⟩

-- ============================================================================
-- PART IV: 140 Auto-Compiled Rescued Epoch-6 Conditional Theorems
-- ============================================================================
theorem auto_rescued_cond_e6_0 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_64 x0 (BBin.pos p1)) = (AutoArena.op_57 x0 (AutoArena.op_57 x2 (BBin.pos p1))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_1 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_64 x0 x2) = (AutoArena.op_57 x0 (AutoArena.op_57 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_2 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 x1 (BBin.pos p0)) = (AutoArena.op_57 x1 (AutoArena.op_57 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_3 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 x1 x2) = (AutoArena.op_57 x1 (AutoArena.op_57 (BBin.pos p0) x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_4 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 x2 (BBin.pos p0)) = (AutoArena.op_57 x2 (AutoArena.op_57 x1 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_5 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 x2 x1) = (AutoArena.op_57 x2 (AutoArena.op_57 (BBin.pos p0) x1)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_6 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_57 x0 (BBin.pos p1))) = (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_57 x2 (BBin.pos p1))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_7 (x0 : BBin) (x1 : BBin) (p2 : BPos) : (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_57 x0 (BBin.pos p2))) = (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_57 x1 (BBin.pos p2))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases x1 with _ | (_ | _ | _) <;> rcases p2 with _ | _ | _ <;> rfl
theorem auto_rescued_cond_e6_8 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_57 x1 (BBin.pos p0))) = (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_57 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_9 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_63 x0 (BBin.pos p1))) = (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_63 x2 (BBin.pos p1))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_10 (x0 : BBin) (x1 : BBin) (p2 : BPos) : (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_63 x0 (BBin.pos p2))) = (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_63 x1 (BBin.pos p2))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases x1 with _ | (_ | _ | _) <;> rcases p2 with _ | _ | _ <;> rfl
theorem auto_rescued_cond_e6_11 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_63 x1 (BBin.pos p0))) = (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_63 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_12 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_72 x0 (BBin.pos p1))) = (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_72 x2 (BBin.pos p1))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_13 (x0 : BBin) (x1 : BBin) (p2 : BPos) : (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_72 x0 (BBin.pos p2))) = (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_72 x1 (BBin.pos p2))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases x1 with _ | (_ | _ | _) <;> rcases p2 with _ | _ | _ <;> rfl
theorem auto_rescued_cond_e6_14 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_72 x1 (BBin.pos p0))) = (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_72 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_15 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_73 (BBin.pos p0) x1)) = (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_73 (BBin.pos p0) x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_16 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_73 x0 (BBin.pos p1))) = (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_73 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_17 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_73 (BBin.pos p0) x1)) = (AutoArena.op_57 (BBin.pos BPos.one) (AutoArena.op_73 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_18 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_63 (BBin.pos p0) x2) (BBin.pos p0)) = (AutoArena.op_57 (AutoArena.op_63 x1 x2) (BBin.pos p0)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_19 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 BBin.zero x1) (BBin.pos p0)) = (AutoArena.op_57 (AutoArena.op_72 x2 x1) (BBin.pos p0)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_20 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p0) (BBin.pos p0)) x1) = (AutoArena.op_57 (AutoArena.op_72 x2 (BBin.pos p0)) x1) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_21 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p0) (BBin.pos p0)) x2) = (AutoArena.op_57 (AutoArena.op_72 x1 (BBin.pos p0)) x2) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_22 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p0) x2) (BBin.pos p0)) = (AutoArena.op_57 (AutoArena.op_72 x1 x2) (BBin.pos p0)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_23 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 x0 (AutoArena.op_63 x0 (BBin.pos p1))) = (AutoArena.op_57 x0 (AutoArena.op_63 x2 (BBin.pos p1))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_24 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 x0 (AutoArena.op_63 x0 x2)) = (AutoArena.op_57 x0 (AutoArena.op_63 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_25 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 x0 (AutoArena.op_63 x2 x2)) = (AutoArena.op_64 x0 (AutoArena.op_72 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_26 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 x0 (AutoArena.op_72 x0 (BBin.pos p1))) = (AutoArena.op_57 x0 (AutoArena.op_72 x2 (BBin.pos p1))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_27 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 x0 (AutoArena.op_72 x0 x2)) = (AutoArena.op_57 x0 (AutoArena.op_72 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_28 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 x0 (AutoArena.op_72 x2 x2)) = (AutoArena.op_64 x0 (AutoArena.op_63 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_29 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 x1 (AutoArena.op_63 (BBin.pos p0) x2)) = (AutoArena.op_57 x1 (AutoArena.op_63 x1 x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_30 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 x1 (AutoArena.op_63 (BBin.pos p0) x2)) = (AutoArena.op_64 x1 (AutoArena.op_72 x2 x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_31 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 x1 (AutoArena.op_63 x1 (BBin.pos p0))) = (AutoArena.op_57 x1 (AutoArena.op_63 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_32 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 x1 (AutoArena.op_63 x2 x2)) = (AutoArena.op_64 x1 (AutoArena.op_72 (BBin.pos p0) x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_33 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 x1 (AutoArena.op_72 (BBin.pos p0) x2)) = (AutoArena.op_57 x1 (AutoArena.op_72 x1 x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_34 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 x1 (AutoArena.op_72 (BBin.pos p0) x2)) = (AutoArena.op_64 x1 (AutoArena.op_63 x2 x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_35 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 x1 (AutoArena.op_72 x1 (BBin.pos p0))) = (AutoArena.op_57 x1 (AutoArena.op_72 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_36 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 x1 (AutoArena.op_72 x2 x2)) = (AutoArena.op_64 x1 (AutoArena.op_63 (BBin.pos p0) x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_37 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 x2 (AutoArena.op_63 BBin.zero x0)) = (AutoArena.op_64 x2 (AutoArena.op_72 (BBin.pos p1) x0)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_38 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 x2 (AutoArena.op_63 BBin.zero x1)) = (AutoArena.op_64 x2 (AutoArena.op_72 (BBin.pos p0) x1)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_39 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 x2 (AutoArena.op_63 (BBin.pos p0) x1)) = (AutoArena.op_57 x2 (AutoArena.op_63 x2 x1)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_40 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 x2 (AutoArena.op_63 (BBin.pos p0) x1)) = (AutoArena.op_64 x2 (AutoArena.op_72 x1 x1)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_41 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 x2 (AutoArena.op_63 x1 (BBin.pos p0))) = (AutoArena.op_57 x2 (AutoArena.op_63 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_42 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 x2 (AutoArena.op_63 (BBin.pos p1) x0)) = (AutoArena.op_64 x2 (AutoArena.op_72 BBin.zero x0)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_43 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 x2 (AutoArena.op_63 (BBin.pos p1) x0)) = (AutoArena.op_64 x2 (AutoArena.op_72 x0 x0)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_44 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 x2 (AutoArena.op_72 BBin.zero x0)) = (AutoArena.op_64 x2 (AutoArena.op_63 (BBin.pos p1) x0)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_45 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 x2 (AutoArena.op_72 BBin.zero x1)) = (AutoArena.op_64 x2 (AutoArena.op_63 (BBin.pos p0) x1)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_46 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 x2 (AutoArena.op_72 (BBin.pos p0) x1)) = (AutoArena.op_57 x2 (AutoArena.op_72 x2 x1)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_47 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 x2 (AutoArena.op_72 (BBin.pos p0) x1)) = (AutoArena.op_64 x2 (AutoArena.op_63 x1 x1)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_48 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 x2 (AutoArena.op_72 x1 (BBin.pos p0))) = (AutoArena.op_57 x2 (AutoArena.op_72 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_49 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 x2 (AutoArena.op_72 (BBin.pos p1) x0)) = (AutoArena.op_64 x2 (AutoArena.op_63 BBin.zero x0)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_50 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 x2 (AutoArena.op_72 (BBin.pos p1) x0)) = (AutoArena.op_64 x2 (AutoArena.op_63 x0 x0)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_51 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_63 (AutoArena.op_63 (BBin.pos p0) x2) (BBin.pos p0)) = (AutoArena.op_63 (AutoArena.op_63 x1 x2) (BBin.pos p0)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_52 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_63 (AutoArena.op_72 BBin.zero x1) (BBin.pos p0)) = (AutoArena.op_63 (AutoArena.op_72 x2 x1) (BBin.pos p0)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_53 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_63 (AutoArena.op_72 (BBin.pos p0) (BBin.pos p0)) x1) = (AutoArena.op_63 (AutoArena.op_72 x2 (BBin.pos p0)) x1) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_54 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_63 (AutoArena.op_72 (BBin.pos p0) (BBin.pos p0)) x2) = (AutoArena.op_63 (AutoArena.op_72 x1 (BBin.pos p0)) x2) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_55 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_63 (AutoArena.op_72 (BBin.pos p0) x2) (BBin.pos p0)) = (AutoArena.op_63 (AutoArena.op_72 x1 x2) (BBin.pos p0)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_56 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_64 (BBin.pos BPos.one) (AutoArena.op_72 x0 (BBin.pos p1))) = (AutoArena.op_64 (BBin.pos BPos.one) (AutoArena.op_72 x2 (BBin.pos p1))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_57 (x0 : BBin) (x1 : BBin) (p2 : BPos) : (AutoArena.op_64 (BBin.pos BPos.one) (AutoArena.op_72 x0 (BBin.pos p2))) = (AutoArena.op_64 (BBin.pos BPos.one) (AutoArena.op_72 x1 (BBin.pos p2))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases x1 with _ | (_ | _ | _) <;> rcases p2 with _ | _ | _ <;> rfl
theorem auto_rescued_cond_e6_58 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (BBin.pos BPos.one) (AutoArena.op_72 x1 (BBin.pos p0))) = (AutoArena.op_64 (BBin.pos BPos.one) (AutoArena.op_72 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_59 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (BBin.pos BPos.one) (AutoArena.op_73 (BBin.pos p0) x1)) = (AutoArena.op_64 (BBin.pos BPos.one) (AutoArena.op_73 (BBin.pos p0) x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_60 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_64 (BBin.pos BPos.one) (AutoArena.op_73 x0 (BBin.pos p1))) = (AutoArena.op_64 (BBin.pos BPos.one) (AutoArena.op_73 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_61 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (BBin.pos BPos.one) (AutoArena.op_73 (BBin.pos p0) x1)) = (AutoArena.op_64 (BBin.pos BPos.one) (AutoArena.op_73 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_62 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_72 BBin.zero (AutoArena.op_72 x2 (BBin.pos p0))) = (AutoArena.op_72 (AutoArena.op_72 x1 x2) (BBin.pos p0)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_63 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_72 BBin.zero (AutoArena.op_73 x2 (BBin.pos p0))) = (AutoArena.op_72 x1 (AutoArena.op_73 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_64 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_72 (AutoArena.op_63 (BBin.pos p0) x2) (BBin.pos p0)) = (AutoArena.op_72 (AutoArena.op_63 x1 x2) (BBin.pos p0)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_65 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_73 (AutoArena.op_63 (BBin.pos p0) x2) (BBin.pos p0)) = (AutoArena.op_73 (AutoArena.op_63 x1 x2) (BBin.pos p0)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_66 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_63 BBin.zero (AutoArena.op_64 x2 (BBin.pos p0))) = (AutoArena.op_57 (AutoArena.op_63 x2 x2) (AutoArena.op_57 x1 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_67 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_63 (BBin.pos BPos.one) (AutoArena.op_73 x2 (BBin.pos p0))) = (AutoArena.op_63 (AutoArena.op_8 x1 BBin.zero) (AutoArena.op_73 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_68 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_63 (BBin.pos p0) (AutoArena.op_64 x2 (BBin.pos p0))) = (AutoArena.op_57 (AutoArena.op_63 (BBin.pos p0) x2) (AutoArena.op_57 x1 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_69 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_63 x1 (AutoArena.op_57 x2 (BBin.pos p0))) = (AutoArena.op_63 (AutoArena.op_64 x1 (BBin.pos p0)) (AutoArena.op_57 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_70 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_63 x1 (AutoArena.op_63 x2 (BBin.pos p0))) = (AutoArena.op_63 (AutoArena.op_64 x1 (BBin.pos p0)) (AutoArena.op_63 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_71 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_63 x1 (AutoArena.op_72 x2 (BBin.pos p0))) = (AutoArena.op_63 (AutoArena.op_64 x1 (BBin.pos p0)) (AutoArena.op_72 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_72 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_63 x2 (AutoArena.op_64 x2 (BBin.pos p0))) = (AutoArena.op_63 (AutoArena.op_64 x2 x1) (AutoArena.op_64 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_73 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_63 x2 (AutoArena.op_64 x2 x1)) = (AutoArena.op_63 (AutoArena.op_64 x2 (BBin.pos p0)) (AutoArena.op_64 x2 x1)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_74 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_72 (BBin.pos p0) x1) (BBin.pos p0)) = (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p0) x1) (AutoArena.op_57 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_75 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_72 (BBin.pos p0) x1) x2) = (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p0) x1) (AutoArena.op_57 (BBin.pos p0) x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_76 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_72 x0 (BBin.pos p1)) x2) = (AutoArena.op_57 (AutoArena.op_72 x0 (BBin.pos p1)) (AutoArena.op_57 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_77 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_72 (BBin.pos p0) x2) (BBin.pos p0)) = (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p0) x2) (AutoArena.op_57 x1 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_78 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_72 (BBin.pos p0) x2) x1) = (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p0) x2) (AutoArena.op_57 (BBin.pos p0) x1)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_79 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_72 x0 x2) (BBin.pos p1)) = (AutoArena.op_57 (AutoArena.op_72 x0 x2) (AutoArena.op_57 x2 (BBin.pos p1))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_80 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_72 (BBin.pos p1) x0) (BBin.pos p1)) = (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p1) x0) (AutoArena.op_57 x2 (BBin.pos p1))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_81 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_72 x1 (BBin.pos p0)) x2) = (AutoArena.op_57 (AutoArena.op_72 x1 (BBin.pos p0)) (AutoArena.op_57 (BBin.pos p0) x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_82 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_72 (BBin.pos p1) x0) x2) = (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p1) x0) (AutoArena.op_57 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_83 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_72 x2 (BBin.pos p0)) x1) = (AutoArena.op_57 (AutoArena.op_72 x2 (BBin.pos p0)) (AutoArena.op_57 (BBin.pos p0) x1)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_84 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_72 x2 x0) (BBin.pos p1)) = (AutoArena.op_57 (AutoArena.op_72 x2 x0) (AutoArena.op_57 x2 (BBin.pos p1))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_85 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_72 x2 x0) x2) = (AutoArena.op_57 (AutoArena.op_72 x2 x0) (AutoArena.op_57 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_86 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_72 x2 x1) (BBin.pos p0)) = (AutoArena.op_57 (AutoArena.op_72 x2 x1) (AutoArena.op_57 x1 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_87 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_72 x2 x1) (BBin.pos p0)) = (AutoArena.op_57 (AutoArena.op_72 x2 x1) (AutoArena.op_57 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_88 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_72 x2 x1) x2) = (AutoArena.op_57 (AutoArena.op_72 x2 x1) (AutoArena.op_57 (BBin.pos p0) x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_89 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_73 (BBin.pos p0) x1) (BBin.pos p0)) = (AutoArena.op_57 (AutoArena.op_73 (BBin.pos p0) x1) (AutoArena.op_57 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_90 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_73 (BBin.pos p0) x1) x2) = (AutoArena.op_57 (AutoArena.op_73 (BBin.pos p0) x1) (AutoArena.op_57 (BBin.pos p0) x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_91 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_73 x0 (BBin.pos p1)) x2) = (AutoArena.op_57 (AutoArena.op_73 x0 (BBin.pos p1)) (AutoArena.op_57 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_92 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_73 (BBin.pos p0) x2) (BBin.pos p0)) = (AutoArena.op_57 (AutoArena.op_73 (BBin.pos p0) x2) (AutoArena.op_57 x1 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_93 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_73 (BBin.pos p0) x2) x1) = (AutoArena.op_57 (AutoArena.op_73 (BBin.pos p0) x2) (AutoArena.op_57 (BBin.pos p0) x1)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_94 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_73 (BBin.pos p1) x0) (BBin.pos p1)) = (AutoArena.op_57 (AutoArena.op_73 (BBin.pos p1) x0) (AutoArena.op_57 x2 (BBin.pos p1))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_95 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_73 x1 (BBin.pos p0)) x2) = (AutoArena.op_57 (AutoArena.op_73 x1 (BBin.pos p0)) (AutoArena.op_57 (BBin.pos p0) x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_96 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_73 (BBin.pos p1) x0) x2) = (AutoArena.op_57 (AutoArena.op_73 (BBin.pos p1) x0) (AutoArena.op_57 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_97 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_73 x2 (BBin.pos p0)) x1) = (AutoArena.op_57 (AutoArena.op_73 x2 (BBin.pos p0)) (AutoArena.op_57 (BBin.pos p0) x1)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_98 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_73 x2 x0) (BBin.pos p1)) = (AutoArena.op_57 (AutoArena.op_73 x2 x0) (AutoArena.op_57 x2 (BBin.pos p1))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_99 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_73 x2 x0) x2) = (AutoArena.op_57 (AutoArena.op_73 x2 x0) (AutoArena.op_57 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_100 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_73 x2 x1) (BBin.pos p0)) = (AutoArena.op_57 (AutoArena.op_73 x2 x1) (AutoArena.op_57 x1 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_101 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_73 x2 x1) (BBin.pos p0)) = (AutoArena.op_57 (AutoArena.op_73 x2 x1) (AutoArena.op_57 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_102 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_64 (AutoArena.op_73 x2 x1) x2) = (AutoArena.op_57 (AutoArena.op_73 x2 x1) (AutoArena.op_57 (BBin.pos p0) x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_103 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_72 x1 (AutoArena.op_57 x2 (BBin.pos p0))) = (AutoArena.op_72 (AutoArena.op_64 x1 (BBin.pos p0)) (AutoArena.op_57 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_104 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_72 x1 (AutoArena.op_63 x2 (BBin.pos p0))) = (AutoArena.op_72 (AutoArena.op_64 x1 (BBin.pos p0)) (AutoArena.op_63 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_105 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_72 x1 (AutoArena.op_72 x2 (BBin.pos p0))) = (AutoArena.op_72 (AutoArena.op_64 x1 (BBin.pos p0)) (AutoArena.op_72 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_106 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_72 x2 (AutoArena.op_63 x1 (BBin.pos p0))) = (AutoArena.op_72 (AutoArena.op_64 x2 (BBin.pos p0)) (AutoArena.op_63 x1 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_107 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_72 x2 (AutoArena.op_72 x1 (BBin.pos p0))) = (AutoArena.op_72 (AutoArena.op_64 x2 (BBin.pos p0)) (AutoArena.op_72 x1 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_108 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_63 x0 x0) (AutoArena.op_72 x0 x2)) = (AutoArena.op_57 (AutoArena.op_63 x0 x0) (AutoArena.op_72 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_109 (x0 : BBin) (x1 : BBin) (p2 : BPos) : (AutoArena.op_57 (AutoArena.op_63 x0 x1) (AutoArena.op_72 x0 (BBin.pos p2))) = (AutoArena.op_57 (AutoArena.op_63 x0 x1) (AutoArena.op_72 x1 (BBin.pos p2))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases x1 with _ | (_ | _ | _) <;> rcases p2 with _ | _ | _ <;> rfl
theorem auto_rescued_cond_e6_110 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_63 x2 x0) (AutoArena.op_63 x0 x2)) = (AutoArena.op_57 (AutoArena.op_63 x2 x0) (AutoArena.op_63 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_111 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_63 x2 x0) (AutoArena.op_72 x0 x2)) = (AutoArena.op_57 (AutoArena.op_63 x2 x0) (AutoArena.op_72 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_112 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 BBin.zero x1) (AutoArena.op_63 x2 x2)) = (AutoArena.op_64 (AutoArena.op_72 x1 x1) (AutoArena.op_72 (BBin.pos p0) x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_113 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p0) (BBin.pos p0)) (AutoArena.op_64 x1 x2)) = (AutoArena.op_57 (AutoArena.op_72 x1 (BBin.pos p0)) (AutoArena.op_64 x1 x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_114 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p0) (BBin.pos p0)) (AutoArena.op_64 x1 x2)) = (AutoArena.op_57 (AutoArena.op_72 x1 (BBin.pos p0)) (AutoArena.op_64 x2 x1)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_115 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p0) (BBin.pos p0)) (AutoArena.op_64 x1 x2)) = (AutoArena.op_57 (AutoArena.op_72 x2 (BBin.pos p0)) (AutoArena.op_64 x1 x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_116 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p0) x1) (AutoArena.op_63 x2 x2)) = (AutoArena.op_64 (AutoArena.op_72 (BBin.pos p0) x1) (AutoArena.op_72 (BBin.pos p0) x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_117 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x0 (BBin.pos p1)) (AutoArena.op_63 x2 x2)) = (AutoArena.op_64 (AutoArena.op_72 x0 (BBin.pos p1)) (AutoArena.op_72 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_118 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x0 (BBin.pos p1)) (AutoArena.op_64 x0 x2)) = (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p1) (BBin.pos p1)) (AutoArena.op_64 x0 x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_119 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x0 (BBin.pos p1)) (AutoArena.op_64 x0 x2)) = (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p1) (BBin.pos p1)) (AutoArena.op_64 x2 x0)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_120 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x0 (BBin.pos p1)) (AutoArena.op_64 x0 x2)) = (AutoArena.op_57 (AutoArena.op_72 x2 (BBin.pos p1)) (AutoArena.op_64 x0 x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_121 (x0 : BBin) (x1 : BBin) (p2 : BPos) : (AutoArena.op_57 (AutoArena.op_72 x0 (BBin.pos p2)) (AutoArena.op_64 x0 x1)) = (AutoArena.op_57 (AutoArena.op_72 x1 (BBin.pos p2)) (AutoArena.op_64 x0 x1)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases x1 with _ | (_ | _ | _) <;> rcases p2 with _ | _ | _ <;> rfl
theorem auto_rescued_cond_e6_122 (x0 : BBin) (x1 : BBin) (p2 : BPos) : (AutoArena.op_57 (AutoArena.op_72 x0 (BBin.pos p2)) (AutoArena.op_64 x0 x1)) = (AutoArena.op_57 (AutoArena.op_72 x1 (BBin.pos p2)) (AutoArena.op_64 x1 x0)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases x1 with _ | (_ | _ | _) <;> rcases p2 with _ | _ | _ <;> rfl
theorem auto_rescued_cond_e6_123 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x0 x2) (AutoArena.op_64 x0 (BBin.pos p1))) = (AutoArena.op_57 (AutoArena.op_72 x2 x2) (AutoArena.op_64 x0 (BBin.pos p1))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_124 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x1 (BBin.pos p0)) (AutoArena.op_63 x2 x2)) = (AutoArena.op_64 (AutoArena.op_72 x1 (BBin.pos p0)) (AutoArena.op_72 (BBin.pos p0) x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_125 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p1) x0) (AutoArena.op_63 x2 x2)) = (AutoArena.op_64 (AutoArena.op_72 (BBin.pos p1) x0) (AutoArena.op_72 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_126 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x1 (BBin.pos p0)) (AutoArena.op_72 x2 x2)) = (AutoArena.op_64 (AutoArena.op_72 x1 (BBin.pos p0)) (AutoArena.op_63 (BBin.pos p0) x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_127 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 (BBin.pos p1) x0) (AutoArena.op_72 x2 x2)) = (AutoArena.op_64 (AutoArena.op_72 (BBin.pos p1) x0) (AutoArena.op_63 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_128 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x2 (BBin.pos p0)) (AutoArena.op_63 BBin.zero x1)) = (AutoArena.op_64 (AutoArena.op_72 x2 (BBin.pos p0)) (AutoArena.op_72 (BBin.pos p0) x1)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_129 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x2 x0) (AutoArena.op_63 x0 (BBin.pos p1))) = (AutoArena.op_57 (AutoArena.op_72 x2 x0) (AutoArena.op_63 x2 (BBin.pos p1))) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_130 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x2 (BBin.pos p0)) (AutoArena.op_63 (BBin.pos p0) x1)) = (AutoArena.op_64 (AutoArena.op_72 x2 (BBin.pos p0)) (AutoArena.op_72 x1 x1)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_131 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x2 x0) (AutoArena.op_63 x0 x2)) = (AutoArena.op_57 (AutoArena.op_72 x2 x0) (AutoArena.op_63 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_132 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x2 x0) (AutoArena.op_63 x2 x2)) = (AutoArena.op_64 (AutoArena.op_72 x2 x0) (AutoArena.op_72 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_133 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x2 x0) (AutoArena.op_72 x0 x2)) = (AutoArena.op_57 (AutoArena.op_72 x2 x0) (AutoArena.op_72 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_134 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x2 x0) (AutoArena.op_72 x2 x2)) = (AutoArena.op_64 (AutoArena.op_72 x2 x0) (AutoArena.op_63 (BBin.pos p1) x2)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_135 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x2 (BBin.pos p1)) (AutoArena.op_63 BBin.zero x0)) = (AutoArena.op_64 (AutoArena.op_72 x2 (BBin.pos p1)) (AutoArena.op_72 (BBin.pos p1) x0)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_136 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x2 x1) (AutoArena.op_63 x1 (BBin.pos p0))) = (AutoArena.op_57 (AutoArena.op_72 x2 x1) (AutoArena.op_63 x2 (BBin.pos p0))) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_137 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x2 (BBin.pos p1)) (AutoArena.op_63 (BBin.pos p1) x0)) = (AutoArena.op_64 (AutoArena.op_72 x2 (BBin.pos p1)) (AutoArena.op_72 BBin.zero x0)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_138 (x0 : BBin) (p1 : BPos) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x2 (BBin.pos p1)) (AutoArena.op_63 (BBin.pos p1) x0)) = (AutoArena.op_64 (AutoArena.op_72 x2 (BBin.pos p1)) (AutoArena.op_72 x0 x0)) := by
  rcases x0 with _ | (_ | _ | _) <;> rcases p1 with _ | _ | _ <;> rcases x2 with _ | (_ | _ | _) <;> rfl
theorem auto_rescued_cond_e6_139 (p0 : BPos) (x1 : BBin) (x2 : BBin) : (AutoArena.op_57 (AutoArena.op_72 x2 x1) (AutoArena.op_63 x2 x2)) = (AutoArena.op_64 (AutoArena.op_72 x2 x1) (AutoArena.op_72 (BBin.pos p0) x2)) := by
  rcases p0 with _ | _ | _ <;> rcases x1 with _ | (_ | _ | _) <;> rcases x2 with _ | (_ | _ | _) <;> rfl

end SiliconBigBang
