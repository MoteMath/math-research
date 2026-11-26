/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LoftqCyclesRank1

/-!
# Verified Solutions (`loftq-cycles-rank1-ef21`)
-/

namespace LoftqCyclesRank1Challenge

open LoftqCyclesRank1

theorem rank1_onebit_ef21_contraction_exact (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    (∀ W : RatMat m n,
      ∃ u : Fin m → Int, ∃ v : Fin n → Int, isSignVec u ∧ isSignVec v ∧
      ∃ γ : Rat, frobSqErr W (rank1Mat γ u v) ≤
        (1 - 1 / ((m * n : Nat) : Rat)) * frobSq W) ∧
    (∃ W : RatMat m n,
      (0 : Rat) < frobSq W ∧
      ∀ u : Fin m → Int, ∀ v : Fin n → Int, isSignVec u → isSignVec v →
      ∀ γ : Rat,
        (1 - 1 / ((m * n : Nat) : Rat)) * frobSq W ≤ frobSqErr W (rank1Mat γ u v)) :=
  LoftqCyclesRank1.rank1_onebit_ef21_contraction_exact m n hm hn

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
         QSqrt2.alpha2x2 * frobSqQ2 W_rot2x2 * QSqrt2.ofInt (vecSqNormInt u * vecSqNormInt v))) :=
  LoftqCyclesRank1.rank1_ternary_2x2_contraction_exact

theorem coupled_orthogonal_beats_block_2x2_rotations :
    (∀ u v : Fin 3 → Int, isTernVec u → isTernVec v →
      quadFormInt W_3x3_coupled u v * quadFormInt W_3x3_coupled u v * 7239976 ≤
        2162403 * (vecSqNormInt u * vecSqNormInt v * frobSqInt W_3x3_coupled)) ∧
    QSqrt2.ofRat (2162403 / 7239976) < QSqrt2.blockUB3 ∧
    isOrthogonalInt W_4x4_coupled 16680999 ∧
    (∀ u v : Fin 4 → Int, isTernVec u → isTernVec v →
      quadFormInt W_4x4_coupled u v * quadFormInt W_4x4_coupled u v * 133447992 ≤
        28440889 * (vecSqNormInt u * vecSqNormInt v * frobSqInt W_4x4_coupled)) ∧
    QSqrt2.ofRat (28440889 / 133447992) < QSqrt2.blockUB4 :=
  LoftqCyclesRank1.coupled_orthogonal_beats_block_2x2_rotations

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
        (absmaxQuantAtScale M (1 / (M : Rat)) x - x) = 1 / (4 * (M : Rat) * (M : Rat)))) :=
  LoftqCyclesRank1.loftq_alternating_monotone_energy_and_4m2_saturation

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
    loftqStepErrQ16 W_cyc2_q16 Q1 * 113 < loftqStepErrQ16 W_cyc2_q16 Q0 * 100 :=
  LoftqCyclesRank1.loftq_explicit_3x3_symmetric_2cycle_witness

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
    loftqStepErrQ16 W_cyc3_q16 Q2 * 106 < loftqStepErrQ16 W_cyc3_q16 Q0 * 100 :=
  LoftqCyclesRank1.loftq_explicit_3x3_symmetric_3cycle_witness

end LoftqCyclesRank1Challenge
