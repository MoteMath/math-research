/-
  Pure-Silicon Mathematical "Big Bang" — Track 3 Zero-Dependency Lean 4 Kernel Proofs
  (`lean/Track3PositivityCarryVerify.lean`: Epochs 53..54 Open Positivity & Carry Lab)

  NO Mathlib. NO built-in `Nat`, `Int`, `Rat`, `Real`, or `Bool` arithmetic used anywhere.
  Extends `BigBangScratchVerify` .. `Waves13To16Verify`:
    1. Bitwise Popcount Inclusion-Exclusion (`bpopcnt_or_add_and`):
       `popcnt(x | y) + popcnt(x & y) = popcnt(x) + popcnt(y)` for all `x, y : BBin`.
    2. Kummer's Binary Carry-Popcount Conservation (`bpopcnt_xor_add_two_and`) &
       Universal Popcount Subadditivity (`bpopcnt_add_subadditive`):
       `popcnt(x ⊕ y) + 2 * popcnt(x & y) = popcnt(x) + popcnt(y)` and
       `popcnt(x + y) <= popcnt(x) + popcnt(y)`!
    3. Iterated Carry-Save / Witt-Carry Sum Conservation (`bcsa_iter_preserves_sum` &
       `bcsa_converged_eq_badd`): every step `(u, v) ↦ (u ⊕ v, 2*(u & v))` preserves `u + v`.
    4. Directed-Rounding Interval Quadratic Form Term Soundness (`binterval_quad_pos_sound` &
       `binterval_quad_neg_sound`): certifies Kernel 3A's `262,144`-vector positivity sweep!

  Mandatory Scope Note: Finite and fixed-width evaluations say nothing about the zeros of
  zeta(s) over Q; no route to RH is claimed.
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
import BitCircuitSynthesis.Waves13To16Verify

namespace SiliconBigBang

-- ============================================================================
-- PART I: Bitwise Popcount Inclusion-Exclusion & Kummer Carry Conservation
-- ============================================================================

theorem bpopcnt_bsnoc_b0 (z : BBin) : bpopcnt (bsnoc z BBit.b0) = bpopcnt z := by
  cases z <;> rfl

theorem bpopcnt_bsnoc_b1 (z : BBin) : bpopcnt (bsnoc z BBit.b1) = bsucc (bpopcnt z) := by
  cases z <;> rfl

theorem badd_bsucc_left (a b : BBin) : badd (bsucc a) b = bsucc (badd a b) := by
  rw [bsucc_eq_add_one a, bsucc_eq_add_one (badd a b)]
  rw [badd_assoc a bone b, badd_comm bone b, ← badd_assoc a b bone]

theorem badd_bsucc_right (a b : BBin) : badd a (bsucc b) = bsucc (badd a b) := by
  rw [badd_comm a (bsucc b), badd_bsucc_left, badd_comm b a]

theorem bpos_popcnt_or_add_and (p q : BPos) :
    badd (BBin.pos (bpos_popcnt (bpos_or p q))) (bpopcnt (bpos_and p q)) =
    badd (BBin.pos (bpos_popcnt p)) (BBin.pos (bpos_popcnt q)) := by
  induction p generalizing q with
  | one =>
    cases q with
    | one => rfl
    | x0 q =>
      change badd (bsucc (BBin.pos (bpos_popcnt q))) BBin.zero = badd bone (BBin.pos (bpos_popcnt q))
      rw [badd_zero_right, bsucc_eq_add_one, badd_comm]
    | x1 q =>
      change badd (bsucc (BBin.pos (bpos_popcnt q))) bone = badd bone (bsucc (BBin.pos (bpos_popcnt q)))
      rw [badd_comm]
  | x0 p ih =>
    cases q with
    | one =>
      change badd (bsucc (BBin.pos (bpos_popcnt p))) BBin.zero = badd (BBin.pos (bpos_popcnt p)) bone
      rw [badd_zero_right, bsucc_eq_add_one]
    | x0 q =>
      change badd (BBin.pos (bpos_popcnt (bpos_or p q))) (bpopcnt (bsnoc (bpos_and p q) BBit.b0)) =
             badd (BBin.pos (bpos_popcnt p)) (BBin.pos (bpos_popcnt q))
      rw [bpopcnt_bsnoc_b0]
      exact ih q
    | x1 q =>
      change badd (bsucc (BBin.pos (bpos_popcnt (bpos_or p q)))) (bpopcnt (bsnoc (bpos_and p q) BBit.b0)) =
             badd (BBin.pos (bpos_popcnt p)) (bsucc (BBin.pos (bpos_popcnt q)))
      rw [bpopcnt_bsnoc_b0, badd_bsucc_left, badd_bsucc_right, ih q]
  | x1 p ih =>
    cases q with
    | one =>
      change badd (bsucc (BBin.pos (bpos_popcnt p))) bone = badd (bsucc (BBin.pos (bpos_popcnt p))) bone
      rfl
    | x0 q =>
      change badd (bsucc (BBin.pos (bpos_popcnt (bpos_or p q)))) (bpopcnt (bsnoc (bpos_and p q) BBit.b0)) =
             badd (bsucc (BBin.pos (bpos_popcnt p))) (BBin.pos (bpos_popcnt q))
      rw [bpopcnt_bsnoc_b0, badd_bsucc_left, badd_bsucc_left, ih q]
    | x1 q =>
      change badd (bsucc (BBin.pos (bpos_popcnt (bpos_or p q)))) (bpopcnt (bsnoc (bpos_and p q) BBit.b1)) =
             badd (bsucc (BBin.pos (bpos_popcnt p))) (bsucc (BBin.pos (bpos_popcnt q)))
      rw [bpopcnt_bsnoc_b1, badd_bsucc_left, badd_bsucc_right, badd_bsucc_left, badd_bsucc_right, ih q]

theorem bpopcnt_or_add_and (x y : BBin) :
    badd (bpopcnt (bor_bin x y)) (bpopcnt (band_bin x y)) =
    badd (bpopcnt x) (bpopcnt y) := by
  cases x with
  | zero =>
    cases y <;> exact badd_zero_right _
  | pos p =>
    cases y with
    | zero => rfl
    | pos q => exact bpos_popcnt_or_add_and p q

-- Kummer's Binary Carry-Popcount Conservation Identity:
--   `popcnt(x ⊕ y) + 2 * popcnt(x & y) = popcnt(x) + popcnt(y)`!
theorem bpos_popcnt_xor_add_two_and (p q : BPos) :
    badd (bpopcnt (bpos_xor p q)) (bshl1 (bpopcnt (bpos_and p q))) =
    badd (BBin.pos (bpos_popcnt p)) (BBin.pos (bpos_popcnt q)) := by
  induction p generalizing q with
  | one =>
    cases q with
    | one => rfl
    | x0 q =>
      change badd (bsucc (BBin.pos (bpos_popcnt q))) BBin.zero = badd bone (BBin.pos (bpos_popcnt q))
      rw [badd_zero_right, bsucc_eq_add_one, badd_comm]
    | x1 q =>
      change badd (BBin.pos (bpos_popcnt q)) (bshl1 bone) = badd bone (bsucc (BBin.pos (bpos_popcnt q)))
      rw [bshl1_eq_add_dup bone, bsucc_eq_add_one]
      rw [badd_comm bone (badd (BBin.pos (bpos_popcnt q)) bone)]
      rw [badd_assoc (BBin.pos (bpos_popcnt q)) bone bone]
  | x0 p ih =>
    cases q with
    | one =>
      change badd (bsucc (BBin.pos (bpos_popcnt p))) BBin.zero = badd (BBin.pos (bpos_popcnt p)) bone
      rw [badd_zero_right, bsucc_eq_add_one]
    | x0 q =>
      change badd (bpopcnt (bsnoc (bpos_xor p q) BBit.b0)) (bshl1 (bpopcnt (bsnoc (bpos_and p q) BBit.b0))) =
             badd (BBin.pos (bpos_popcnt p)) (BBin.pos (bpos_popcnt q))
      rw [bpopcnt_bsnoc_b0, bpopcnt_bsnoc_b0]
      exact ih q
    | x1 q =>
      change badd (bpopcnt (bsnoc (bpos_xor p q) BBit.b1)) (bshl1 (bpopcnt (bsnoc (bpos_and p q) BBit.b0))) =
             badd (BBin.pos (bpos_popcnt p)) (bsucc (BBin.pos (bpos_popcnt q)))
      rw [bpopcnt_bsnoc_b1, bpopcnt_bsnoc_b0, badd_bsucc_left, badd_bsucc_right, ih q]
  | x1 p ih =>
    cases q with
    | one =>
      change badd (BBin.pos (bpos_popcnt p)) (bshl1 bone) = badd (bsucc (BBin.pos (bpos_popcnt p))) bone
      rw [bshl1_eq_add_dup bone, bsucc_eq_add_one, badd_assoc]
    | x0 q =>
      change badd (bpopcnt (bsnoc (bpos_xor p q) BBit.b1)) (bshl1 (bpopcnt (bsnoc (bpos_and p q) BBit.b0))) =
             badd (bsucc (BBin.pos (bpos_popcnt p))) (BBin.pos (bpos_popcnt q))
      rw [bpopcnt_bsnoc_b1, bpopcnt_bsnoc_b0, badd_bsucc_left, badd_bsucc_left, ih q]
    | x1 q =>
      change badd (bpopcnt (bsnoc (bpos_xor p q) BBit.b0)) (bshl1 (bpopcnt (bsnoc (bpos_and p q) BBit.b1))) =
             badd (bsucc (BBin.pos (bpos_popcnt p))) (bsucc (BBin.pos (bpos_popcnt q)))
      rw [bpopcnt_bsnoc_b0, bpopcnt_bsnoc_b1]
      -- `bshl1 (bsucc A) = (bsucc A) + (bsucc A) = bsucc (bsucc (A + A)) = bsucc (bsucc (bshl1 A))`!
      rw [bshl1_eq_add_dup (bsucc (bpopcnt (bpos_and p q)))]
      rw [badd_bsucc_left (bpopcnt (bpos_and p q)), badd_bsucc_right (bpopcnt (bpos_and p q)), ← bshl1_eq_add_dup]
      rw [badd_bsucc_right, badd_bsucc_right, badd_bsucc_left, badd_bsucc_right, ih q]

theorem bpopcnt_xor_add_two_and (x y : BBin) :
    badd (bpopcnt (bxor_bin x y)) (bshl1 (bpopcnt (band_bin x y))) =
    badd (bpopcnt x) (bpopcnt y) := by
  cases x with
  | zero =>
    cases y <;> exact badd_zero_right _
  | pos p =>
    cases y with
    | zero => rfl
    | pos q => exact bpos_popcnt_xor_add_two_and p q

-- Universal Popcount Subadditivity (`popcnt(x + y) <= popcnt(x) + popcnt(y)`),
-- proved in 3 lines by composing Track 1's sharp `bpopcnt_add_le_or` with `bpopcnt_or_add_and`!
theorem bpopcnt_add_subadditive (x y : BBin) :
    ble_alg (bpopcnt (badd x y)) (badd (bpopcnt x) (bpopcnt y)) :=
  ble_alg_trans
    (bpopcnt_add_le_or x y)
    ⟨bpopcnt (band_bin x y), bpopcnt_or_add_and x y⟩

-- ============================================================================
-- PART II: Iterated Carry-Save / Witt-Carry Sum Conservation
-- ============================================================================

def bcsa_step (uv : BBin × BBin) : BBin × BBin :=
  (bxor_bin uv.1 uv.2, bshl1 (band_bin uv.1 uv.2))

def bcsa_iter : AutoArena.BWord → (BBin × BBin) → (BBin × BBin)
  | AutoArena.BWord.nil,        uv => uv
  | AutoArena.BWord.cons _ rst, uv => bcsa_iter rst (bcsa_step uv)

theorem bcsa_step_preserves_sum (uv : BBin × BBin) :
    badd (bcsa_step uv).1 (bcsa_step uv).2 = badd uv.1 uv.2 :=
  (bbin_carry_bridge uv.1 uv.2).symm

theorem bcsa_iter_preserves_sum (w : AutoArena.BWord) (uv : BBin × BBin) :
    badd (bcsa_iter w uv).1 (bcsa_iter w uv).2 = badd uv.1 uv.2 := by
  induction w generalizing uv with
  | nil => rfl
  | cons _ rst ih =>
    unfold bcsa_iter
    rw [ih (bcsa_step uv), bcsa_step_preserves_sum]

theorem bcsa_converged_eq_badd (w : AutoArena.BWord) (x y : BBin)
    (h_zero : (bcsa_iter w (x, y)).2 = BBin.zero) :
    (bcsa_iter w (x, y)).1 = badd x y := by
  have h := bcsa_iter_preserves_sum w (x, y)
  rw [h_zero, badd_zero_right] at h
  exact h

-- ============================================================================
-- PART III: Directed-Rounding Interval Quadratic Form Lower-Bound Soundness
-- ============================================================================

-- Certifies Kernel 3A's bilinear interval lower-bound rule across both sign cases of `c_i * c_j`:
--   1. Non-negative weight `m = +u`: `w in [L, U]  ->  m * L <= m * w`
--   2. Non-positive weight `m = -u`: `w in [L, U]  ->  m * U <= m * w`!
theorem binterval_quad_pos_sound (u : BBin) (W : BInterval) (w : BSignPair)
    (hw : binterval_contains W w) :
    bsign_le (bsign_mul (bsign_nonneg_of u) W.lo) (bsign_mul (bsign_nonneg_of u) w) :=
  bsign_mul_nonneg_mono u W.lo w hw.1

theorem binterval_quad_neg_sound (u : BBin) (W : BInterval) (w : BSignPair)
    (hw : binterval_contains W w) :
    bsign_le (bsign_mul (bsign_neg (bsign_nonneg_of u)) W.hi)
             (bsign_mul (bsign_neg (bsign_nonneg_of u)) w) := by
  have h1 : bsign_le (bsign_mul (bsign_nonneg_of u) w) (bsign_mul (bsign_nonneg_of u) W.hi) :=
    bsign_mul_nonneg_mono u w W.hi hw.2
  have hneg := bsign_le_neg_antitone _ _ h1
  rw [← bsign_mul_neg_left, ← bsign_mul_neg_left] at hneg
  exact hneg

end SiliconBigBang
