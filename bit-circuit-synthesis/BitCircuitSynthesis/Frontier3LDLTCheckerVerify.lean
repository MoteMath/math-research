/-
  Pure-Silicon Mathematical "Big Bang" — Frontier 3 Zero-Dependency Lean 4 Proofs
  (`lean/Frontier3LDLTCheckerVerify.lean`: Epochs 61..64 Arbitrary-Dimension `LDL^T`
  Sum-of-Squares Positivity Checker & Skew-Palindromic Dipole Pole-Annihilation)

  NO Mathlib. NO built-in `Nat`, `Int`, `Rat`, `Real`, or `Bool` arithmetic used anywhere.
  Extends `BigBangScratchVerify` .. `AutoInductiveArenaVerify`:
    1. Exact `BPos` & `BSignPair` Canonical Trichotomy (`bpos_trichotomy`, `bsign_trichotomy`)
       and Universal Square Positivity (`bsign_sq_nonneg`, `bsign_sq_pos_of_ne_zero`).
    2. Arbitrary-Dimension `BVec` / `BMat` Unit-Triangular `LDL^T` Sum-of-Squares Positivity
       Checker (`bldlt_sos_nonneg_universal` & `bldlt_utri_strict_pos_universal`):
       Proves for ALL dimensions `N` that `d_0, ..., d_{N-1} > 0` and `c ≠ 0` imply
       `Q(c) = ∑_k d_k (L^T c)_k^2 >= 1 > 0`!
    3. Arbitrary-Dimension Skew-Palindromic Dipole Pole-Annihilation Theorem
       (`bskew_dipole_annihilates_even_pole`): formally explains the odd-parity dipole wave
       autonomously evolved by the 16,384 GPU walkers at wide support `p^m <= 509`!

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
import BitCircuitSynthesis.Track3PositivityCarryVerify
import BitCircuitSynthesis.Frontier1ModularityWittVerify
import BitCircuitSynthesis.AutoInductiveArenaVerify

namespace SiliconBigBang

-- ============================================================================
-- PART I: `BPos` & `BSignPair` Trichotomy and Universal Square Positivity
-- ============================================================================

def bpos_dbl_pred : BPos → BPos
  | BPos.one  => BPos.one
  | BPos.x0 q => BPos.x1 (bpos_dbl_pred q)
  | BPos.x1 q => BPos.x1 (BPos.x0 q)

theorem bpos_succ_dbl_pred (q : BPos) : bpos_succ (bpos_dbl_pred q) = BPos.x0 q := by
  induction q with
  | one => rfl
  | x0 q ih => dsimp only [bpos_dbl_pred, bpos_succ]; rw [ih]
  | x1 q _ => rfl

theorem bpos_x0_eq_add_dup (p : BPos) : BPos.x0 p = bpos_add p p := by
  induction p with
  | one => rfl
  | x0 p ih => dsimp only [bpos_add]; rw [← ih]
  | x1 p ih => dsimp only [bpos_add]; rw [bpos_add_carry_eq_succ_add, ← ih]; rfl

theorem bpos_trichotomy (p q : BPos) :
    (p = q) ∨ (∃ d : BPos, p = bpos_add q d) ∨ (∃ d : BPos, q = bpos_add p d) := by
  induction p generalizing q with
  | one =>
    cases q with
    | one => exact Or.inl rfl
    | x0 q => exact Or.inr (Or.inr ⟨bpos_dbl_pred q, (bpos_succ_dbl_pred q).symm⟩)
    | x1 q => exact Or.inr (Or.inr ⟨BPos.x0 q, rfl⟩)
  | x0 p ih =>
    cases q with
    | one => exact Or.inr (Or.inl ⟨bpos_dbl_pred p, (bpos_succ_dbl_pred p).symm⟩)
    | x0 q =>
      rcases ih q with rfl | ⟨d, rfl⟩ | ⟨d, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨BPos.x0 d, rfl⟩)
      · exact Or.inr (Or.inr ⟨BPos.x0 d, rfl⟩)
    | x1 q =>
      rcases ih q with rfl | ⟨d, rfl⟩ | ⟨d, rfl⟩
      · exact Or.inr (Or.inr ⟨BPos.one, rfl⟩)
      · refine Or.inr (Or.inl ⟨bpos_dbl_pred d, ?_⟩)
        -- Need `BPos.x0 (bpos_add q d) = bpos_add (BPos.x1 q) (bpos_dbl_pred d)`!
        have h1 : bpos_add (BPos.x1 q) (bpos_dbl_pred d) =
                  bpos_add (bpos_succ (BPos.x0 q)) (bpos_dbl_pred d) := rfl
        rw [h1, bpos_add_succ_left, ← bpos_add_succ_right, bpos_succ_dbl_pred]; rfl
      · exact Or.inr (Or.inr ⟨BPos.x1 d, rfl⟩)
  | x1 p ih =>
    cases q with
    | one => exact Or.inr (Or.inl ⟨BPos.x0 p, rfl⟩)
    | x0 q =>
      rcases ih q with rfl | ⟨d, rfl⟩ | ⟨d, rfl⟩
      · exact Or.inr (Or.inl ⟨BPos.one, rfl⟩)
      · exact Or.inr (Or.inl ⟨BPos.x1 d, rfl⟩)
      · refine Or.inr (Or.inr ⟨bpos_dbl_pred d, ?_⟩)
        have h1 : bpos_add (BPos.x1 p) (bpos_dbl_pred d) =
                  bpos_add (bpos_succ (BPos.x0 p)) (bpos_dbl_pred d) := rfl
        rw [h1, bpos_add_succ_left, ← bpos_add_succ_right, bpos_succ_dbl_pred]; rfl
    | x1 q =>
      rcases ih q with rfl | ⟨d, rfl⟩ | ⟨d, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨BPos.x0 d, rfl⟩)
      · exact Or.inr (Or.inr ⟨BPos.x0 d, rfl⟩)

theorem bsign_trichotomy (z : BSignPair) :
    bsign_equiv z bsign_zero ∨
    (∃ p : BPos, bsign_equiv z (bsign_nonneg_of (BBin.pos p))) ∨
    (∃ p : BPos, bsign_equiv z (bsign_neg (bsign_nonneg_of (BBin.pos p)))) := by
  rcases z with ⟨a, b⟩
  cases a with
  | zero =>
    cases b with
    | zero => exact Or.inl rfl
    | pos q => exact Or.inr (Or.inr ⟨q, rfl⟩)
  | pos p =>
    cases b with
    | zero => exact Or.inr (Or.inl ⟨p, rfl⟩)
    | pos q =>
      rcases bpos_trichotomy p q with rfl | ⟨d, rfl⟩ | ⟨d, rfl⟩
      · refine Or.inl ?_
        unfold bsign_equiv bsign_zero; dsimp only
        exact badd_zero_right (BBin.pos p)
      · refine Or.inr (Or.inl ⟨d, ?_⟩)
        unfold bsign_equiv bsign_nonneg_of; dsimp only
        rw [badd_zero_right]
        change BBin.pos (bpos_add q d) = BBin.pos (bpos_add d q)
        rw [bpos_add_comm]
      · refine Or.inr (Or.inr ⟨d, ?_⟩)
        unfold bsign_equiv bsign_neg bsign_nonneg_of; dsimp only
        rfl

theorem bsign_nonneg_mul (u v : BBin) :
    bsign_mul (bsign_nonneg_of u) (bsign_nonneg_of v) = bsign_nonneg_of (bmul u v) := by
  unfold bsign_nonneg_of bsign_mul
  have hz (w : BBin) : bmul w BBin.zero = BBin.zero := by cases w <;> rfl
  have hzl (w : BBin) : bmul BBin.zero w = BBin.zero := rfl
  simp only [hz, hzl, badd_zero_right]

theorem bsign_zero_le_nonneg (u : BBin) : bsign_le bsign_zero (bsign_nonneg_of u) :=
  ⟨u, by unfold bsign_zero bsign_add bsign_nonneg_of; dsimp only; exact bsign_equiv_refl _⟩

theorem bsign_pos_ge_one (p : BPos) :
    bsign_le (bsign_nonneg_of (BBin.pos BPos.one)) (bsign_nonneg_of (BBin.pos p)) := by
  rcases bpos_trichotomy p BPos.one with rfl | ⟨d, rfl⟩ | ⟨d, hd⟩
  · exact bsign_le_refl _
  · refine ⟨BBin.pos d, ?_⟩
    rw [bsign_nonneg_add]
    exact bsign_equiv_refl _
  · -- Impossible: `BPos.one = bpos_add p d` is never `one`!
    exfalso
    cases p with
    | one => cases d <;> cases hd
    | x0 p => cases d <;> cases hd
    | x1 p => cases d <;> cases hd

theorem bsign_sq_pos_of_ne_zero (z : BSignPair) (hz : ¬ bsign_equiv z bsign_zero) :
    ∃ p : BPos, bsign_equiv (bsign_mul z z) (bsign_nonneg_of (BBin.pos p)) := by
  rcases bsign_trichotomy z with h0 | ⟨p, hp⟩ | ⟨p, hn⟩
  · exact absurd h0 hz
  · refine ⟨bpos_mul p p, ?_⟩
    have hsq := bsign_mul_congr _ _ _ _ hp hp
    rw [bsign_nonneg_mul] at hsq
    exact hsq
  · refine ⟨bpos_mul p p, ?_⟩
    have hsq := bsign_mul_congr _ _ _ _ hn hn
    rw [bsign_mul_neg_left, bsign_mul_neg_right, bsign_neg_invol, bsign_nonneg_mul] at hsq
    exact hsq

theorem bsign_sq_nonneg (z : BSignPair) : bsign_le bsign_zero (bsign_mul z z) := by
  rcases bsign_trichotomy z with h0 | ⟨p, hp⟩ | ⟨p, hn⟩
  · have hsq : bsign_equiv (bsign_mul z z) bsign_zero := by
      apply bsign_equiv_trans _ (bsign_mul bsign_zero bsign_zero) _
      · exact bsign_mul_congr _ _ _ _ h0 h0
      · exact bsign_equiv_refl _
    exact bsign_le_congr_both (bsign_equiv_refl _) (bsign_equiv_symm _ _ hsq) (bsign_le_refl bsign_zero)
  · have hsq := bsign_mul_congr _ _ _ _ hp hp
    rw [bsign_nonneg_mul] at hsq
    exact bsign_le_congr_both (bsign_equiv_refl _) (bsign_equiv_symm _ _ hsq) (bsign_zero_le_nonneg _)
  · have hsq := bsign_mul_congr _ _ _ _ hn hn
    rw [bsign_mul_neg_left, bsign_mul_neg_right, bsign_neg_invol, bsign_nonneg_mul] at hsq
    exact bsign_le_congr_both (bsign_equiv_refl _) (bsign_equiv_symm _ _ hsq) (bsign_zero_le_nonneg _)

-- ============================================================================
-- PART II: Arbitrary-Dimension `BVec` / `BMat` `LDL^T` Positivity Checker
-- ============================================================================

inductive BVec : Type where
  | vnil  : BVec
  | vcons : BSignPair → BVec → BVec

inductive BMat : Type where
  | mnil  : BMat
  | mcons : BVec → BMat → BMat

def bvec_dot : BVec → BVec → BSignPair
  | BVec.vnil,       _          => bsign_zero
  | _,               BVec.vnil  => bsign_zero
  | BVec.vcons x xs, BVec.vcons y ys => bsign_add (bsign_mul x y) (bvec_dot xs ys)

def bldlt_sos_eval : BVec → BMat → BVec → BSignPair
  | BVec.vnil,       _,                _ => bsign_zero
  | _,               BMat.mnil,        _ => bsign_zero
  | BVec.vcons dk ds, BMat.mcons rk rs, c =>
      let yk := bvec_dot rk c
      bsign_add (bsign_mul dk (bsign_mul yk yk)) (bldlt_sos_eval ds rs c)

def bvec_all_nonneg : BVec → Prop
  | BVec.vnil       => True
  | BVec.vcons x xs => (∃ u : BBin, bsign_equiv x (bsign_nonneg_of u)) ∧ bvec_all_nonneg xs

def bvec_all_pos : BVec → Prop
  | BVec.vnil       => True
  | BVec.vcons x xs => (∃ p : BPos, bsign_equiv x (bsign_nonneg_of (BBin.pos p))) ∧ bvec_all_pos xs

def bvec_all_zero : BVec → Prop
  | BVec.vnil       => True
  | BVec.vcons x xs => bsign_equiv x bsign_zero ∧ bvec_all_zero xs

theorem bvec_all_pos_imp_nonneg (d : BVec) (h : bvec_all_pos d) : bvec_all_nonneg d := by
  induction d with
  | vnil => trivial
  | vcons x xs ih =>
    rcases h with ⟨⟨p, hp⟩, hxs⟩
    exact ⟨⟨BBin.pos p, hp⟩, ih hxs⟩

-- Theorem 3C.1: Universal Arbitrary-Dimension `LDL^T` Sum-of-Squares Non-Negativity!
theorem bldlt_sos_nonneg_universal (d : BVec) (rows : BMat) (c : BVec)
    (hd : bvec_all_nonneg d) :
    bsign_le bsign_zero (bldlt_sos_eval d rows c) := by
  induction d generalizing rows with
  | vnil => exact bsign_le_refl bsign_zero
  | vcons dk ds ih =>
    cases rows with
    | mnil => exact bsign_le_refl bsign_zero
    | mcons rk rs =>
      rcases hd with ⟨⟨u, hu⟩, hds⟩
      dsimp only [bldlt_sos_eval]
      have h_tail := ih rs hds
      have h_sq   := bsign_sq_nonneg (bvec_dot rk c)
      have h_mul0 := bsign_mul_nonneg_mono u bsign_zero (bsign_mul (bvec_dot rk c) (bvec_dot rk c)) h_sq
      have hz0 : bsign_mul (bsign_nonneg_of u) bsign_zero = bsign_zero := by
        change bsign_mul (bsign_nonneg_of u) (bsign_nonneg_of BBin.zero) = bsign_zero
        rw [bsign_nonneg_mul]
        have hmz : bmul u BBin.zero = BBin.zero := by cases u <;> rfl
        rw [hmz]; rfl
      rw [hz0] at h_mul0
      have h_head : bsign_le bsign_zero (bsign_mul dk (bsign_mul (bvec_dot rk c) (bvec_dot rk c))) :=
        bsign_le_congr_both (bsign_equiv_refl _)
          (bsign_mul_congr _ _ _ _ (bsign_equiv_symm _ _ hu) (bsign_equiv_refl _)) h_mul0
      have h_sum := bsign_le_add_mono _ _ _ _ h_head h_tail
      rw [bsign_add_zero_right] at h_sum
      exact h_sum

-- Unit-upper-triangular `LDL^T` factor `(d_k, l_k)` where `(L^T c)_k = c_k + (l_k · c_tail)`!

inductive BUtriFactor : Type where
  | unil  : BUtriFactor
  | ucons : BSignPair → BVec → BUtriFactor → BUtriFactor -- `(d_k, l_k, rest)`

def butri_sos_eval : BUtriFactor → BVec → BSignPair
  | BUtriFactor.unil,            _                 => bsign_zero
  | _,                           BVec.vnil         => bsign_zero
  | BUtriFactor.ucons dk lk rst, BVec.vcons ck cs  =>
      let yk := bsign_add ck (bvec_dot lk cs)
      bsign_add (bsign_mul dk (bsign_mul yk yk)) (butri_sos_eval rst cs)

def butri_pivots_pos : BUtriFactor → Prop
  | BUtriFactor.unil            => True
  | BUtriFactor.ucons dk _ rst  =>
      (∃ p : BPos, bsign_equiv dk (bsign_nonneg_of (BBin.pos p))) ∧ butri_pivots_pos rst

theorem bvec_dot_zero_right (l c : BVec) (hc : bvec_all_zero c) :
    bsign_equiv (bvec_dot l c) bsign_zero := by
  induction l generalizing c with
  | vnil => exact bsign_equiv_refl _
  | vcons x xs ih =>
    cases c with
    | vnil => exact bsign_equiv_refl _
    | vcons y ys =>
      rcases hc with ⟨hy0, hys⟩
      dsimp only [bvec_dot]
      have hm0 : bsign_equiv (bsign_mul x y) bsign_zero :=
        bsign_equiv_trans _ (bsign_mul x bsign_zero) _
          (bsign_mul_congr _ _ _ _ (bsign_equiv_refl x) hy0)
          (by unfold bsign_mul bsign_zero; dsimp only
              have hz (w : BBin) : bmul w BBin.zero = BBin.zero := by cases w <;> rfl
              simp only [hz, badd_zero_right]; exact rfl)
      have ht0 := ih ys hys
      exact bsign_equiv_trans _ (bsign_add bsign_zero bsign_zero) _
        (bsign_add_congr _ _ _ _ hm0 ht0) (bsign_equiv_refl _)

theorem butri_sos_nonneg (F : BUtriFactor) (c : BVec) (hF : butri_pivots_pos F) :
    bsign_le bsign_zero (butri_sos_eval F c) := by
  induction F generalizing c with
  | unil => exact bsign_le_refl bsign_zero
  | ucons dk lk rst ih =>
    cases c with
    | vnil => exact bsign_le_refl bsign_zero
    | vcons ck cs =>
      rcases hF with ⟨⟨p, hp⟩, hrst⟩
      dsimp only [butri_sos_eval]
      have ht := ih cs hrst
      let yk := bsign_add ck (bvec_dot lk cs)
      have hsq := bsign_sq_nonneg yk
      have hm  := bsign_mul_nonneg_mono (BBin.pos p) bsign_zero (bsign_mul yk yk) hsq
      have hz0 : bsign_mul (bsign_nonneg_of (BBin.pos p)) bsign_zero = bsign_zero := by
        unfold bsign_nonneg_of bsign_zero bsign_mul; dsimp only; rfl
      rw [hz0] at hm
      have hh : bsign_le bsign_zero (bsign_mul dk (bsign_mul yk yk)) :=
        bsign_le_congr_both (bsign_equiv_refl _)
          (bsign_mul_congr _ _ _ _ (bsign_equiv_symm _ _ hp) (bsign_equiv_refl _)) hm
      have hsum := bsign_le_add_mono _ _ _ _ hh ht
      rw [bsign_add_zero_right] at hsum
      exact hsum

theorem bvec_zero_decidable (c : BVec) : bvec_all_zero c ∨ ¬ bvec_all_zero c := by
  induction c with
  | vnil => exact Or.inl trivial
  | vcons x xs ih =>
    rcases bsign_trichotomy x with hx0 | ⟨p, hp⟩ | ⟨p, hn⟩
    · rcases ih with hxs0 | hxs_nz
      · exact Or.inl ⟨hx0, hxs0⟩
      · exact Or.inr (fun h => hxs_nz h.2)
    · refine Or.inr (fun h => ?_)
      have h0p := bsign_equiv_trans _ x _ (bsign_equiv_symm _ _ hp) h.1
      exact bsign_pos_not_le_zero p (bsign_le_congr_both (bsign_equiv_refl _) h0p (bsign_le_refl _))
    · refine Or.inr (fun h => ?_)
      have h0n := bsign_equiv_trans _ (bsign_neg x) _
        (bsign_equiv_symm _ _ (bsign_equiv_trans _ (bsign_neg (bsign_neg (bsign_nonneg_of (BBin.pos p)))) _
          (bsign_equiv_neg_congr _ _ hn) (by rw [bsign_neg_invol]; exact bsign_equiv_refl _)))
        (bsign_equiv_neg_congr _ _ h.1)
      exact bsign_pos_not_le_zero p (bsign_le_congr_both (bsign_equiv_refl _) h0n (bsign_le_refl _))

inductive BSameLen : BUtriFactor → BVec → Prop where
  | nil  : BSameLen BUtriFactor.unil BVec.vnil
  | cons {dk lk rst ck cs} : BSameLen rst cs → BSameLen (BUtriFactor.ucons dk lk rst) (BVec.vcons ck cs)

-- Theorem 3C.2: Universal Arbitrary-Dimension Unit-Triangular `LDL^T` Strict Positivity Theorem!
-- For ANY dimension `N`, ANY factor `F` with strictly positive pivots (`d_k > 0`), and ANY non-zero
-- integer vector `c ≠ 0` of matching length, `Q(c) >= 1 > 0` (`¬ bsign_equiv Q(c) 0`)!
theorem bldlt_utri_strict_pos_universal (F : BUtriFactor) (c : BVec)
    (hlen : BSameLen F c)
    (hF   : butri_pivots_pos F)
    (hnz  : ¬ bvec_all_zero c) :
    bsign_le (bsign_nonneg_of (BBin.pos BPos.one)) (butri_sos_eval F c) ∧
    ¬ bsign_equiv (butri_sos_eval F c) bsign_zero := by
  have hge1 : bsign_le (bsign_nonneg_of (BBin.pos BPos.one)) (butri_sos_eval F c) := by
    induction hlen with
    | nil => exact absurd trivial hnz
    | @cons dk lk rst ck cs hsub ih =>
      rcases hF with ⟨⟨p, hp⟩, hrst⟩
      dsimp only [butri_sos_eval]
      rcases bvec_zero_decidable cs with hcs_zero | hcs_nz
      · -- `cs` is all zero => `ck` CANNOT be zero (else `c` is all zero!), and `bvec_dot lk cs ≈ 0`,
        -- so `yk = ck + (lk · cs) ≈ ck ≠ 0`, hence `dk * yk^2 >= 1` and tail `>= 0`!
        have hck_nz : ¬ bsign_equiv ck bsign_zero := fun hck0 => hnz ⟨hck0, hcs_zero⟩
        have hdot0  := bvec_dot_zero_right lk cs hcs_zero
        let yk := bsign_add ck (bvec_dot lk cs)
        have hyk_eq : bsign_equiv yk ck :=
          bsign_equiv_trans _ (bsign_add ck bsign_zero) _
            (bsign_add_congr _ _ _ _ (bsign_equiv_refl ck) hdot0)
            (by rw [bsign_add_zero_right]; exact bsign_equiv_refl ck)
        have hyk_nz : ¬ bsign_equiv yk bsign_zero :=
          fun hy0 => hck_nz (bsign_equiv_trans _ yk _ (bsign_equiv_symm _ _ hyk_eq) hy0)
        rcases bsign_sq_pos_of_ne_zero yk hyk_nz with ⟨q, hq⟩
        have hprod : bsign_equiv (bsign_mul dk (bsign_mul yk yk))
                                 (bsign_nonneg_of (BBin.pos (bpos_mul p q))) := by
          have hm := bsign_mul_congr _ _ _ _ hp hq
          rw [bsign_nonneg_mul] at hm
          exact hm
        have hhead_ge1 : bsign_le (bsign_nonneg_of (BBin.pos BPos.one))
                                  (bsign_mul dk (bsign_mul yk yk)) :=
          bsign_le_congr_both (bsign_equiv_refl _) (bsign_equiv_symm _ _ hprod)
            (bsign_pos_ge_one (bpos_mul p q))
        have htail_ge0 := butri_sos_nonneg rst cs hrst
        have hsum := bsign_le_add_mono _ _ _ _ hhead_ge1 htail_ge0
        rw [bsign_add_zero_right] at hsum
        exact hsum
      · -- `cs` has a non-zero coordinate => by IH `butri_sos_eval rst cs >= 1`, and head `>= 0`!
        have htail_ge1 := ih hrst hcs_nz
        let yk := bsign_add ck (bvec_dot lk cs)
        have hsq := bsign_sq_nonneg yk
        have hm  := bsign_mul_nonneg_mono (BBin.pos p) bsign_zero (bsign_mul yk yk) hsq
        have hz0 : bsign_mul (bsign_nonneg_of (BBin.pos p)) bsign_zero = bsign_zero := by
          unfold bsign_nonneg_of bsign_zero bsign_mul; dsimp only; rfl
        rw [hz0] at hm
        have hhead_ge0 : bsign_le bsign_zero (bsign_mul dk (bsign_mul yk yk)) :=
          bsign_le_congr_both (bsign_equiv_refl _)
            (bsign_mul_congr _ _ _ _ (bsign_equiv_symm _ _ hp) (bsign_equiv_refl _)) hm
        have hsum := bsign_le_add_mono _ _ _ _ hhead_ge0 htail_ge1
        have hz_left : bsign_add bsign_zero (bsign_nonneg_of (BBin.pos BPos.one)) =
                       bsign_nonneg_of (BBin.pos BPos.one) := by
          rw [bsign_add_comm, bsign_add_zero_right]
        rw [hz_left] at hsum
        exact hsum
  refine ⟨hge1, fun h_eq0 => ?_⟩
  exact bsign_pos_not_le_zero BPos.one
    (bsign_le_congr_both (bsign_equiv_refl _) h_eq0 hge1)

-- ============================================================================
-- PART III: Arbitrary-Dimension Skew-Palindromic Dipole Pole-Annihilation
-- ============================================================================

def bvec_snoc : BVec → BSignPair → BVec
  | BVec.vnil,       z => BVec.vcons z BVec.vnil
  | BVec.vcons x xs, z => BVec.vcons x (bvec_snoc xs z)

def bvec_rev : BVec → BVec
  | BVec.vnil       => BVec.vnil
  | BVec.vcons x xs => bvec_snoc (bvec_rev xs) x

-- Inductive witness of a skew-palindromic dipole `(c_k = -c_{N-1-k})` paired with an
-- even-palindromic pole profile `(w_k = +w_{N-1-k})` across arbitrary dimension `N`:
inductive BSkewEvenPair : BVec → BVec → Prop where
  | empty  : BSkewEvenPair BVec.vnil BVec.vnil
  | center (w0 : BSignPair) : BSkewEvenPair (BVec.vcons bsign_zero BVec.vnil) (BVec.vcons w0 BVec.vnil)
  | wrap   (c_edge w_edge : BSignPair) (c_mid w_mid : BVec)
           (h_mid : BSkewEvenPair c_mid w_mid) :
           BSkewEvenPair
             (BVec.vcons c_edge (bvec_snoc c_mid (bsign_neg c_edge)))
             (BVec.vcons w_edge (bvec_snoc w_mid w_edge))

inductive BSameVecLen : BVec → BVec → Prop where
  | nil  : BSameVecLen BVec.vnil BVec.vnil
  | cons {x y : BSignPair} {xs ys : BVec} :
         BSameVecLen xs ys → BSameVecLen (BVec.vcons x xs) (BVec.vcons y ys)

theorem bvec_snoc_same_len {c w : BVec} (h : BSameVecLen c w) (a b : BSignPair) :
    BSameVecLen (bvec_snoc c a) (bvec_snoc w b) := by
  induction h with
  | nil => exact BSameVecLen.cons BSameVecLen.nil
  | cons _ ih => exact BSameVecLen.cons ih

theorem bskew_even_same_len {c w : BVec} (h : BSkewEvenPair c w) : BSameVecLen c w := by
  induction h with
  | empty => exact BSameVecLen.nil
  | center _ => exact BSameVecLen.cons BSameVecLen.nil
  | wrap ce we _ _ _ ih => exact BSameVecLen.cons (bvec_snoc_same_len ih (bsign_neg ce) we)

theorem bvec_dot_snoc_same_len {c w : BVec} (h : BSameVecLen c w) (a b : BSignPair) :
    bvec_dot (bvec_snoc c a) (bvec_snoc w b) = bsign_add (bvec_dot c w) (bsign_mul a b) := by
  induction h with
  | nil =>
    dsimp only [bvec_snoc, bvec_dot]
    rw [bsign_add_zero_right, bsign_add_comm bsign_zero, bsign_add_zero_right]
  | cons _ ih =>
    dsimp only [bvec_snoc, bvec_dot]
    rw [ih, bsign_add_assoc]

-- Theorem 3C.3: Universal Skew-Palindromic Dipole Pole-Annihilation Theorem!
-- Every odd-parity skew-palindromic vector `c` (`c_k = -c_{N-1-k}`) has `bvec_dot c w ≈ 0`
-- against EVERY even-palindromic pole vector `w` (`w_k = w_{N-1-k}`), explaining why the
-- 16,384 RX 7900 XTX evolutionary walkers evolved `[-1, -4, ..., -15, ..., +15, ..., +4, +1]`!
theorem bskew_dipole_annihilates_even_pole {c w : BVec} (h : BSkewEvenPair c w) :
    bsign_equiv (bvec_dot c w) bsign_zero := by
  induction h with
  | empty => exact bsign_equiv_refl _
  | center w0 =>
    dsimp only [bvec_dot]
    rw [bsign_add_zero_right]
    exact rfl
  | wrap ce we cm wm hmid ih =>
    dsimp only [bvec_dot]
    rw [bvec_dot_snoc_same_len (bskew_even_same_len hmid) (bsign_neg ce) we]
    rw [bsign_mul_neg_left]
    -- `(ce*we) + ((cm · wm) + -(ce*we))` -> `(cm · wm) + ((ce*we) + -(ce*we))`!
    rw [← bsign_add_assoc (bsign_mul ce we) (bvec_dot cm wm) (bsign_neg (bsign_mul ce we))]
    rw [bsign_add_comm (bsign_mul ce we) (bvec_dot cm wm)]
    rw [bsign_add_assoc (bvec_dot cm wm) (bsign_mul ce we) (bsign_neg (bsign_mul ce we))]
    apply bsign_equiv_trans _ (bsign_add bsign_zero bsign_zero) _
    · exact bsign_add_congr _ _ _ _ ih (bsign_add_neg_cancel (bsign_mul ce we))
    · exact bsign_equiv_refl _

end SiliconBigBang
