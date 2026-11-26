/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LoftqCyclesRank1.Defs

/-!
# Trusted Challenge Statements (`loftq-cycles-rank1-ef21`)

Universal and exact pure-`Init` (zero Mathlib) Lean 4 statements for:
1. Universal exact rank-1 1-bit sign EF21 matrix contraction `α = 1 / (m * n)` for all `m, n ≥ 1`.
2. Exact algebraic `(2, 2)` rank-1 ternary EF21 contraction `α = (2 + √2) / 8` over `ℚ(√2)`.
3. Explicit coupled integer/orthogonal matrices at `n = 3, 4` strictly beating block-diagonal `I_k ⊗ R(π/8)`.
4. LoftQ Euclidean-projection monotone energy descent, `Ω(d σ^2 / M^2)` spiked separation, and exact `4M^2` saturation.
5. Exact kernel-checked `3 × 3` symmetric LoftQ permanent 2-cycle witness `W_cyc2`.
6. Exact kernel-checked `3 × 3` symmetric LoftQ permanent 3-cycle witness `W_cyc3`.
-/

namespace LoftqCyclesRank1Challenge

open LoftqCyclesRank1

/-- Theorem 1 (Exact Universal Rank-1 1-Bit Sign EF21 Contraction):
    For all `m, n ≥ 1`, optimal rank-1 1-bit (`{±γ} u v^T`) EF21 compression over `ℚ^{m × n}`
    achieves universal contraction `α = 1 / (m * n)` with exact attainment on `e_0 e_0^T`. -/
theorem rank1_onebit_ef21_contraction_exact (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    (∀ W : RatMat m n,
      ∃ u : Fin m → Int, ∃ v : Fin n → Int, isSignVec u ∧ isSignVec v ∧
      ∃ γ : Rat, frobSqErr W (rank1Mat γ u v) ≤
        (1 - 1 / ((m * n : Nat) : Rat)) * frobSq W) ∧
    (∃ W : RatMat m n,
      (0 : Rat) < frobSq W ∧
      ∀ u : Fin m → Int, ∀ v : Fin n → Int, isSignVec u → isSignVec v →
      ∀ γ : Rat,
        (1 - 1 / ((m * n : Nat) : Rat)) * frobSq W ≤ frobSqErr W (rank1Mat γ u v)) := by
  sorry

/-- Theorem 2 (Exact `(2, 2)` Rank-1 Ternary EF21 Contraction Constant `(2 + √2) / 8`):
    Universal exact lower bound over `ℚ^{2 × 2}` and exact attainment by the `R(π/8)` rotation
    matrix `W_rot2x2 = [[1, √2 - 1], [-(√2 - 1), 1]]` over `QSqrt2 = ℚ(√2)`. -/
theorem rank1_ternary_2x2_contraction_exact :
    (∀ W : RatMat 2 2,
      ∃ u v : Fin 2 → Int, isTernVec u ∧ isTernVec v ∧
        QSqrt2.alpha2x2 * QSqrt2.ofRat (frobSq W) * QSqrt2.ofInt (vecSqNormInt u * vecSqNormInt v) ≤
        QSqrt2.ofRat (quadFormRat W u v * quadFormRat W u v)) ∧
    (frobSqQ2 W_rot2x2 = ⟨8, -4⟩ ∧
     QSqrt2.alpha2x2 * frobSqQ2 W_rot2x2 = QSqrt2.one ∧
     (∀ u v : Fin 2 → Int, isTernVec u → isTernVec v →
       quadFormQ2 W_rot2x2 u v * quadFormQ2 W_rot2x2 u v ≤
         QSqrt2.alpha2x2 * frobSqQ2 W_rot2x2 * QSqrt2.ofInt (vecSqNormInt u * vecSqNormInt v)) ∧
     (∃ u v : Fin 2 → Int, isTernVec u ∧ isTernVec v ∧
       quadFormQ2 W_rot2x2 u v * quadFormQ2 W_rot2x2 u v =
         QSqrt2.alpha2x2 * frobSqQ2 W_rot2x2 * QSqrt2.ofInt (vecSqNormInt u * vecSqNormInt v))) := by
  sorry

/-- Theorem 3 (Coupled Orthogonal / Integer Matrices Strictly Beat Block-Diagonal `I_k ⊗ R(π/8)`):
    `W_3x3_coupled` achieves `≤ 2162403 / 7239976 < (9 + 4√2) / 49`, and `W_4x4_coupled` is
    exact orthogonal (`W^T W = 16680999 · I_4`) achieving `≤ 28440889 / 133447992 < (2 + √2) / 16`. -/
theorem coupled_orthogonal_beats_block_2x2_rotations :
    (∀ u v : Fin 3 → Int, isTernVec u → isTernVec v →
      quadFormInt W_3x3_coupled u v * quadFormInt W_3x3_coupled u v * 7239976 ≤
        2162403 * (vecSqNormInt u * vecSqNormInt v * frobSqInt W_3x3_coupled)) ∧
    QSqrt2.ofRat (2162403 / 7239976) < QSqrt2.blockUB3 ∧
    isOrthogonalInt W_4x4_coupled 16680999 ∧
    (∀ u v : Fin 4 → Int, isTernVec u → isTernVec v →
      quadFormInt W_4x4_coupled u v * quadFormInt W_4x4_coupled u v * 133447992 ≤
        28440889 * (vecSqNormInt u * vecSqNormInt v * frobSqInt W_4x4_coupled)) ∧
    QSqrt2.ofRat (28440889 / 133447992) < QSqrt2.blockUB4 := by
  sorry

/-- Theorem 4 (LoftQ Alternating Monotone Energy, Spiked Separation & Exact `4M^2` Saturation):
    Proves universal Euclidean-projection Lyapunov descent, exact `Ω(d σ^2 / M^2)` spiked-matrix
    separation vs 1-shot, and the exact `4M^2` saturation barrier (`uniformBulkVarianceRatio M = 4M^2`
    and tight worst-case discrete-grid error `1 / (4M^2)` on `[-1, 1]`). -/
theorem loftq_alternating_monotone_energy_and_4m2_saturation :
    (∀ {m n : Nat} (W Q_t Q_next L_t L_next : RatMat m n)
        (S_Q S_L : RatMat m n → Prop),
      S_Q Q_t → S_L L_t →
      isBestApprox S_Q (matSub W L_t) Q_next →
      isBestApprox S_L (matSub W Q_next) L_next →
      frobSqErr W (matAdd Q_next L_next) ≤ frobSqErr W (matAdd Q_next L_t) ∧
      frobSqErr W (matAdd Q_next L_t) ≤ frobSqErr W (matAdd Q_t L_t)) ∧
    (∀ (d M k : Nat), 3 ≤ d → 0 < M → 2 ≤ k →
      let W := spikedDiag d M k
      let Q1 : RatMat d d := fun i j => absmaxQuantAtScale M (2 * k : Rat) (W i j)
      let L1 : RatMat d d := diagMat (fun i => if i.val = 1 then ((k - 1 : Nat) : Rat) else 0)
      let Lalt : RatMat d d := diagMat (fun i => if i.val = 0 then (2 * M * k : Rat) else 0)
      let Qalt : RatMat d d := fun i j => absmaxQuantAtScale M (((k - 1 : Nat) : Rat) / (M : Rat)) (matSub W Lalt i j)
      frobSqErr W (matAdd Q1 L1) =
        ((d - 2 : Nat) : Rat) * (((k - 1 : Nat) : Rat) * ((k - 1 : Nat) : Rat)) ∧
      frobSqErr W (matAdd Qalt Lalt) = 0) ∧
    (∀ M : Nat, 0 < M →
      uniformBulkVarianceRatio M = 4 * (M : Rat) * (M : Rat) ∧
      (∀ x : Rat, absRat x ≤ 1 →
        (absmaxQuantAtScale M (1 / (M : Rat)) x - x) *
        (absmaxQuantAtScale M (1 / (M : Rat)) x - x) ≤ 1 / (4 * (M : Rat) * (M : Rat))) ∧
      (∃ x : Rat, absRat x ≤ 1 ∧
        (absmaxQuantAtScale M (1 / (M : Rat)) x - x) *
        (absmaxQuantAtScale M (1 / (M : Rat)) x - x) = 1 / (4 * (M : Rat) * (M : Rat)))) := by
  sorry

/-- Theorem 5 (Exact `3 × 3` Symmetric LoftQ Permanent 2-Cycle Witness `W_cyc2`):
    Kernel-checked verification that `W_cyc2 = [[149, 91, 350], [91, 920, 978], [350, 978, 297]]`
    enters a permanent period-2 limit cycle at iteration `12` with a `> 13%` non-monotone error jump
    on every odd step (`79857264812871 -> 90566258557330`). -/
theorem loftq_explicit_3x3_symmetric_2cycle_witness :
    let Q0 : Sym3 := ⟨17880998, 0, 17880998, 0, 17880998, -17880998⟩
    let Q1 : Sym3 := ⟨0, 0, 18518972, 0, 18518972, -18518972⟩
    loftqIterQ16 W_cyc2_q16 zeroSym3 12 = Q0 ∧
    loftqStepQ16 W_cyc2_q16 Q0 = Q1 ∧
    loftqStepQ16 W_cyc2_q16 Q1 = Q0 ∧
    Q1 ≠ Q0 ∧
    (∀ t : Nat,
      loftqIterQ16 W_cyc2_q16 zeroSym3 (12 + t + 2) = loftqIterQ16 W_cyc2_q16 zeroSym3 (12 + t) ∧
      loftqIterQ16 W_cyc2_q16 zeroSym3 (12 + t + 1) ≠ loftqIterQ16 W_cyc2_q16 zeroSym3 (12 + t)) ∧
    loftqStepErrQ16 W_cyc2_q16 Q0 = 90566258557330 ∧
    loftqStepErrQ16 W_cyc2_q16 Q1 = 79857264812871 ∧
    loftqStepErrQ16 W_cyc2_q16 Q1 * 113 < loftqStepErrQ16 W_cyc2_q16 Q0 * 100 := by
  sorry

/-- Theorem 6 (Exact `3 × 3` Symmetric LoftQ Permanent 3-Cycle Witness `W_cyc3`):
    Kernel-checked verification that `W_cyc3 = [[-671, -527, 370], [-527, 259, -458], [370, -458, -906]]`
    enters a permanent period-3 limit cycle at iteration `10` through 3 pairwise-distinct states
    with a `> 6%` non-monotone error jump every 3rd step. -/
theorem loftq_explicit_3x3_symmetric_3cycle_witness :
    let Q0 : Sym3 := ⟨-34190948, -34190948, 0, 34190948, -34190948, 0⟩
    let Q1 : Sym3 := ⟨-34910879, -34910879, 0, 0, -34910879, 0⟩
    let Q2 : Sym3 := ⟨-34361399, -34361399, 0, 0, -34361399, 0⟩
    loftqIterQ16 W_cyc3_q16 zeroSym3 10 = Q0 ∧
    loftqStepQ16 W_cyc3_q16 Q0 = Q1 ∧
    loftqStepQ16 W_cyc3_q16 Q1 = Q2 ∧
    loftqStepQ16 W_cyc3_q16 Q2 = Q0 ∧
    Q0 ≠ Q1 ∧ Q1 ≠ Q2 ∧ Q2 ≠ Q0 ∧
    (∀ t : Nat,
      loftqIterQ16 W_cyc3_q16 zeroSym3 (10 + t + 3) = loftqIterQ16 W_cyc3_q16 zeroSym3 (10 + t) ∧
      loftqIterQ16 W_cyc3_q16 zeroSym3 (10 + t + 1) ≠ loftqIterQ16 W_cyc3_q16 zeroSym3 (10 + t) ∧
      loftqIterQ16 W_cyc3_q16 zeroSym3 (10 + t + 2) ≠ loftqIterQ16 W_cyc3_q16 zeroSym3 (10 + t)) ∧
    loftqStepErrQ16 W_cyc3_q16 Q0 = 313694815279071 ∧
    loftqStepErrQ16 W_cyc3_q16 Q1 = 299386514317059 ∧
    loftqStepErrQ16 W_cyc3_q16 Q2 = 295290317881961 ∧
    loftqStepErrQ16 W_cyc3_q16 Q2 * 106 < loftqStepErrQ16 W_cyc3_q16 Q0 * 100 := by
  sorry

end LoftqCyclesRank1Challenge
