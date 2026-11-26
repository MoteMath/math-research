/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NsaBallBoundMoba.RatOrder

/-!
# Theorem 1: `MoBA` / `NSA` Mean-Key Antipodal-Pair & Buried-Needle Blindspot

Proves that for ALL dimensions `d`, ALL block sizes `B ≥ 2` (antipodal pair) and
`B ≥ 3` (buried needle), and ALL nonzero integer queries `q` (`0 < ‖q‖_2^2`),
block-mean selection (`MoBA` / `NSA`) assigns block-mean score `q^T S_b ≤ 0`
(and rational mean score `(q^T S_b) / B ≤ 0`) even while the block contains a
needle key `k_0 = +2q` with `q^T k_0 = 2 ‖q‖_2^2 > 0`, forcing `0%` worst-case
needle recall against any positive-mean distractor block.
-/

namespace NsaBallBoundMoba

theorem intFinSum_antipodal {B : Nat} (hB : 2 ≤ B) (v : Int) :
    intFinSum (fun j : Fin B =>
      if j.val = 0 then 2 * v else if j.val = 1 then -(2 * v) else 0) = 0 := by
  unfold intFinSum
  have haux : ∀ k : Nat, 2 ≤ k →
      intFinSumAux k (fun j : Fin k =>
        if j.val = 0 then 2 * v else if j.val = 1 then -(2 * v) else 0) = 0 := by
    intro k hk
    induction k with
    | zero => omega
    | succ m ih =>
      cases m with
      | zero => omega
      | succ m' =>
        cases m' with
        | zero =>
          simp [intFinSumAux]
          omega
        | succ m'' =>
          rw [intFinSumAux]
          have hih := ih (by omega)
          rw [hih]
          have hne1 : m'' + 1 + 1 ≠ 1 := by omega
          simp [hne1]
  exact haux B hB

theorem intFinSum_buried {B : Nat} (hB : 1 ≤ B) (v : Int) :
    intFinSum (fun j : Fin B =>
      if j.val = 0 then 2 * v else -v) = (3 - (B : Int)) * v := by
  unfold intFinSum
  have haux : ∀ k : Nat, 1 ≤ k →
      intFinSumAux k (fun j : Fin k =>
        if j.val = 0 then 2 * v else -v) = (3 - (k : Int)) * v := by
    intro k hk
    induction k with
    | zero => omega
    | succ m ih =>
      cases m with
      | zero =>
        simp only [intFinSumAux]
        grind
      | succ m' =>
        rw [intFinSumAux]
        have hih := ih (by omega)
        rw [hih]
        simp
        grind
  exact haux B hB

theorem antipodalBlock_sum_zero {d B : Nat} (hB : 2 ≤ B) (q : Fin d → Int) :
    blockSum (antipodalBlock B q) = fun _ => 0 := by
  funext c
  unfold blockSum antipodalBlock
  exact intFinSum_antipodal hB (q c)

theorem antipodalBlock_mean_score_zero {d B : Nat} (hB : 2 ≤ B) (q : Fin d → Int) :
    dotInt q (blockSum (antipodalBlock B q)) = 0 := by
  rw [antipodalBlock_sum_zero hB q]
  exact dotInt_zero_right q

theorem antipodalBlock_needle_score {d B : Nat} (hB : 2 ≤ B) (q : Fin d → Int) :
    dotInt q (antipodalBlock B q ⟨0, by omega⟩) = 2 * normSqInt q := by
  unfold antipodalBlock normSqInt
  have h : (fun c => if (⟨0, by omega⟩ : Fin B).val = 0 then 2 * q c
                     else if (⟨0, by omega⟩ : Fin B).val = 1 then -(2 * q c) else 0) =
           (fun c => 2 * q c) := by
    funext c; rfl
  rw [h, dotInt_smul_right]

theorem buriedNeedleBlock_sum {d B : Nat} (hB : 1 ≤ B) (q : Fin d → Int) :
    blockSum (buriedNeedleBlock B q) = fun c => (3 - (B : Int)) * q c := by
  funext c
  unfold blockSum buriedNeedleBlock
  exact intFinSum_buried hB (q c)

theorem buriedNeedleBlock_mean_score {d B : Nat} (hB : 1 ≤ B) (q : Fin d → Int) :
    dotInt q (blockSum (buriedNeedleBlock B q)) = (3 - (B : Int)) * normSqInt q := by
  rw [buriedNeedleBlock_sum hB q]
  unfold normSqInt
  exact dotInt_smul_right (3 - (B : Int)) q q

theorem buriedNeedleBlock_needle_score {d B : Nat} (hB : 1 ≤ B) (q : Fin d → Int) :
    dotInt q (buriedNeedleBlock B q ⟨0, by omega⟩) = 2 * normSqInt q := by
  unfold buriedNeedleBlock normSqInt
  have h : (fun c => if (⟨0, by omega⟩ : Fin B).val = 0 then 2 * q c else -(q c)) =
           (fun c => 2 * q c) := by
    funext c; rfl
  rw [h, dotInt_smul_right]

theorem nat_cast_rat_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := by
  induction n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    have h1 : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
    rw [h1]
    exact rat_add_nonneg ih (by decide)

theorem nat_cast_rat_pos {n : Nat} (hn : 1 ≤ n) : (0 : Rat) < (n : Rat) := by
  cases n with
  | zero => omega
  | succ k =>
    have h1 : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by grind
    rw [h1]
    have hge : (1 : Rat) ≤ (k : Rat) + 1 := by
      have := rat_add_le_add (nat_cast_rat_nonneg k) (Rat.le_refl (a := (1 : Rat)))
      rw [Rat.zero_add] at this
      exact this
    have h01 : (0 : Rat) < (1 : Rat) := by decide
    have hle : (0 : Rat) ≤ (k : Rat) + 1 := Rat.le_trans (Rat.le_of_lt h01) hge
    have hne : (0 : Rat) ≠ (k : Rat) + 1 := by
      intro heq
      rw [← heq] at hge
      exact Rat.not_le.mpr h01 hge
    exact Rat.lt_of_le_of_ne hle hne

theorem int_nonpos_cast_rat {x : Int} (hx : x ≤ 0) : (x : Rat) ≤ (0 : Rat) := by
  have hk : ∃ k : Nat, x = -(k : Int) := ⟨(-x).toNat, by omega⟩
  rcases hk with ⟨k, rfl⟩
  have hcast : ∀ n : Nat, ((-(n : Int) : Int) : Rat) = -(n : Rat) := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih =>
      have heq : -((m + 1 : Nat) : Int) = -(m : Int) - 1 := by omega
      rw [heq]
      have h1 : ((-(m : Int) - 1 : Int) : Rat) = ((-(m : Int) : Int) : Rat) - 1 := by grind
      have h2 : -((m + 1 : Nat) : Rat) = -(m : Rat) - 1 := by grind
      rw [h1, ih, h2]
  rw [hcast k]
  have hnn := nat_cast_rat_nonneg k
  apply rat_le_of_sub_nonneg
  have heq : (0 : Rat) - -(k : Rat) = (k : Rat) := by grind
  rw [heq]
  exact hnn

theorem int_nonpos_div_nat_pos_rat {x : Int} {B : Nat} (hx : x ≤ 0) (hB : 1 ≤ B) :
    (x : Rat) / (B : Rat) ≤ 0 := by
  have hBpos : (0 : Rat) < (B : Rat) := nat_cast_rat_pos hB
  have hxrat : (x : Rat) ≤ (0 : Rat) := int_nonpos_cast_rat hx
  apply rat_le_of_mul_pos_right hBpos
  rw [rat_div_mul_cancel (Rat.ne_of_gt hBpos)]
  have h0 : (0 : Rat) * (B : Rat) = 0 := by grind
  rw [h0]
  exact hxrat

/-- Headline Theorem 1 (`moba_antipodal_and_buried_needle_blindspot_exact`):
    Exact integer and rational proof of the `MoBA` / `NSA` Mean-Key selection blindspot:
    1. **Antipodal pair (`B ≥ 2`):** `q^T S_b = 0` and `(q^T S_b) / B = 0 ≤ 0`, while
       `k_0 = +2q` attains `q^T k_0 = 2 ‖q‖_2^2 > 0`, so ANY distractor block with
       `q^T S_dist > 0` strictly outranks the needle block (`0%` worst-case recall).
    2. **Buried needle (`B ≥ 3`):** `q^T S_b = (3 - B) ‖q‖_2^2 ≤ 0` (strictly `< 0` for
       all `B ≥ 4`, including `B ∈ {16, 32, 64}`) and `(q^T S_b) / B ≤ 0`, while
       `k_0 = +2q` still attains `q^T k_0 = 2 ‖q‖_2^2 > 0`. -/
theorem moba_antipodal_and_buried_needle_blindspot_exact :
    (∀ (d B : Nat) (q : Fin d → Int), 2 ≤ B → 0 < normSqInt q →
      dotInt q (blockSum (antipodalBlock B q)) = 0 ∧
      ((dotInt q (blockSum (antipodalBlock B q)) : Rat) / (B : Rat) ≤ 0) ∧
      (∃ j : Fin B, dotInt q (antipodalBlock B q j) = 2 * normSqInt q ∧
                    0 < dotInt q (antipodalBlock B q j)) ∧
      (∀ S_dist : Fin d → Int, 0 < dotInt q S_dist →
        dotInt q (blockSum (antipodalBlock B q)) < dotInt q S_dist)) ∧
    (∀ (d B : Nat) (q : Fin d → Int), 3 ≤ B → 0 < normSqInt q →
      dotInt q (blockSum (buriedNeedleBlock B q)) = (3 - (B : Int)) * normSqInt q ∧
      dotInt q (blockSum (buriedNeedleBlock B q)) ≤ 0 ∧
      ((dotInt q (blockSum (buriedNeedleBlock B q)) : Rat) / (B : Rat) ≤ 0) ∧
      (4 ≤ B → dotInt q (blockSum (buriedNeedleBlock B q)) < 0) ∧
      (∃ j : Fin B, dotInt q (buriedNeedleBlock B q j) = 2 * normSqInt q ∧
                    0 < dotInt q (buriedNeedleBlock B q j))) := by
  constructor
  · intro d B q hB hq
    have hsum := antipodalBlock_mean_score_zero hB q
    refine ⟨hsum, ?_, ?_, ?_⟩
    · rw [hsum]
      exact int_nonpos_div_nat_pos_rat (Int.le_refl 0) (by omega)
    · refine ⟨⟨0, by omega⟩, antipodalBlock_needle_score hB q, ?_⟩
      rw [antipodalBlock_needle_score hB q]
      omega
    · intro S_dist hdist
      rw [hsum]
      exact hdist
  · intro d B q hB hq
    have hsum := buriedNeedleBlock_mean_score (B := B) (by omega) q
    have hle : dotInt q (blockSum (buriedNeedleBlock B q)) ≤ 0 := by
      rw [hsum]
      have hneg : 0 ≤ ((B : Int) - 3) * normSqInt q := Int.mul_nonneg (by omega) (by omega)
      have heq : (3 - (B : Int)) * normSqInt q = -(((B : Int) - 3) * normSqInt q) := by grind
      omega
    refine ⟨hsum, hle, int_nonpos_div_nat_pos_rat hle (by omega), ?_, ?_⟩
    · intro hB4
      rw [hsum]
      have hpos : 0 < ((B : Int) - 3) * normSqInt q := Int.mul_pos (by omega) hq
      have hneg : (3 - (B : Int)) * normSqInt q = -(((B : Int) - 3) * normSqInt q) := by grind
      omega
    · refine ⟨⟨0, by omega⟩, buriedNeedleBlock_needle_score (B := B) (by omega) q, ?_⟩
      rw [buriedNeedleBlock_needle_score (B := B) (by omega) q]
      omega

end NsaBallBoundMoba
