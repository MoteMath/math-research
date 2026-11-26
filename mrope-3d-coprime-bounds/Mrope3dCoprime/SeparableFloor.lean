/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mrope3dCoprime.RatOrder

/-!
# Theorems 1 & 2: Separable-Axis Floor Theorem & Coupled-3D Barrier Shattering

Pure-`Init` (zero Mathlib, zero `native_decide`) proofs of:
1. `separable_3d_mrope_axis_floor_theorem`: universal `(P - min(PT, PH, PW) + M_min) / P` floor,
   exact `48/64 = 3/4` floor for Qwen2-VL `(16, 24, 24)`, pigeonhole nonnegative-average guarantee,
   and unconditional Gram/Parseval Dirichlet-Welch lower bound `3/4 - 1/(4(N - 1))`.
2. `coupled_3d_mrope_shatters_separable_floor`: elimination of the additive axis floor via
   coupled 3D phases, exact algebraic 64-pair `Z_4^3` zero-sidelobe witness, and exact algebraic
   27-pair all-nonzero-axis `{1, 2, 3}^3` witness with `|K| ≤ 1/3 < 1/2 < 3/4`.
-/

namespace Mrope3dCoprime

/-! ### Part 1: Separable-Axis Floor Helpers -/

theorem sepAxisSum_zero {P : Nat} (c : Fin P → Int → Rat) (h0 : ∀ k : Fin P, c k 0 = 1) :
    sepAxisSum P c 0 = (P : Rat) := by
  unfold sepAxisSum
  rw [finSum_congr h0, finSum_ones]

theorem sep3DKernel_pure_T {PT PH PW : Nat}
    (cT : Fin PT → Int → Rat) (cH : Fin PH → Int → Rat) (cW : Fin PW → Int → Rat)
    (hH0 : ∀ k, cH k 0 = 1) (hW0 : ∀ k, cW k 0 = 1) (dT : Int) :
    sep3DKernel PT PH PW cT cH cW dT 0 0 =
      (((PH + PW : Nat) : Rat) + sepAxisSum PT cT dT) / ((PT + PH + PW : Nat) : Rat) := by
  unfold sep3DKernel
  rw [sepAxisSum_zero cH hH0, sepAxisSum_zero cW hW0]
  congr 1
  rw [Rat.natCast_add]
  grind

theorem sep3DKernel_pure_H {PT PH PW : Nat}
    (cT : Fin PT → Int → Rat) (cH : Fin PH → Int → Rat) (cW : Fin PW → Int → Rat)
    (hT0 : ∀ k, cT k 0 = 1) (hW0 : ∀ k, cW k 0 = 1) (dH : Int) :
    sep3DKernel PT PH PW cT cH cW 0 dH 0 =
      (((PT + PW : Nat) : Rat) + sepAxisSum PH cH dH) / ((PT + PH + PW : Nat) : Rat) := by
  unfold sep3DKernel
  rw [sepAxisSum_zero cT hT0, sepAxisSum_zero cW hW0]
  congr 1
  rw [Rat.natCast_add]
  grind

theorem sep3DKernel_pure_W {PT PH PW : Nat}
    (cT : Fin PT → Int → Rat) (cH : Fin PH → Int → Rat) (cW : Fin PW → Int → Rat)
    (hT0 : ∀ k, cT k 0 = 1) (hH0 : ∀ k, cH k 0 = 1) (dW : Int) :
    sep3DKernel PT PH PW cT cH cW 0 0 dW =
      (((PT + PH : Nat) : Rat) + sepAxisSum PW cW dW) / ((PT + PH + PW : Nat) : Rat) := by
  unfold sep3DKernel
  rw [sepAxisSum_zero cT hT0, sepAxisSum_zero cH hH0]
  congr 1
  rw [Rat.natCast_add]

/-- Parseval / Gram identity: `∑_{t, s} ⟨v_t, v_s⟩ = ‖∑_t v_t‖^2 ≥ 0`. -/
theorem gram_double_sum_nonneg {N d : Nat} (v : Fin N → Fin d → Rat) :
    (0 : Rat) ≤ finSum (fun t : Fin N => finSum (fun s : Fin N => dotProd (v t) (v s))) := by
  have heq : finSum (fun t : Fin N => finSum (fun s : Fin N => dotProd (v t) (v s))) =
      l2NormSq (fun j : Fin d => finSum (fun t : Fin N => v t j)) := by
    unfold l2NormSq dotProd
    have h1 : ∀ t : Fin N,
        finSum (fun s : Fin N => finSum (fun j : Fin d => v t j * v s j)) =
        finSum (fun j : Fin d => finSum (fun s : Fin N => v t j * v s j)) :=
      fun t => finSum_swap (fun s j => v t j * v s j)
    rw [finSum_congr h1, finSum_swap]
    apply finSum_congr
    intro j
    have h2 : ∀ t : Fin N,
        finSum (fun s : Fin N => v t j * v s j) = v t j * finSum (fun s : Fin N => v s j) :=
      fun t => finSum_mul_left (v t j) (fun s => v s j)
    rw [finSum_congr h2, finSum_mul_right]
  rw [heq]
  unfold l2NormSq dotProd
  apply finSum_nonneg
  intro j
  exact rat_sq_nonneg _

/-- Exact Dirichlet-Welch off-diagonal lower bound for Gram-represented kernels:
    for `N ≥ 2` vectors `v : Fin N → Fin d → Rat` with `‖v_t‖^2 = P`, there exist distinct
    indices `t ≠ s` with `⟨v_t, v_s⟩ ≥ -P / (N - 1)`. -/
theorem gram_welch_offdiag_lower_bound {N d : Nat} (hN : 2 ≤ N) (P : Rat)
    (v : Fin N → Fin d → Rat) (hdiag : ∀ t : Fin N, l2NormSq (v t) = P) :
    ∃ t s : Fin N, t ≠ s ∧ -(P / ((N - 1 : Nat) : Rat)) ≤ dotProd (v t) (v s) := by
  have hsum_nonneg : (0 : Rat) ≤
      finSum (fun t : Fin N => finSum (fun s : Fin N => dotProd (v t) (v s))) :=
    gram_double_sum_nonneg v
  apply Classical.byContradiction
  intro hnone
  have hall : ∀ t s : Fin N, t ≠ s → dotProd (v t) (v s) < -(P / ((N - 1 : Nat) : Rat)) := by
    intro t s hne
    have hnot : ¬ (-(P / ((N - 1 : Nat) : Rat)) ≤ dotProd (v t) (v s)) :=
      fun h => hnone ⟨t, s, hne, h⟩
    exact Rat.not_le.mp hnot
  have hN1_pos : (0 : Rat) < ((N - 1 : Nat) : Rat) := rat_natCast_pos (by omega)
  have hN1_ne : ((N - 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hN1_pos
  -- Each row `t` has diagonal `P` and `N - 1` off-diagonal entries each strictly `< -P/(N-1)`.
  have hrow_neg : ∀ t : Fin N, finSum (fun s : Fin N => dotProd (v t) (v s)) < 0 := by
    intro t
    let c : Rat := -(P / ((N - 1 : Nat) : Rat))
    have hbound : ∀ s : Fin N, dotProd (v t) (v s) ≤ (if s = t then P else c) := by
      intro s
      by_cases hst : s = t
      · simp only [hst, ite_true]
        have hd : dotProd (v t) (v t) = P := hdiag t
        rw [hd]; exact Rat.le_refl
      · simp only [hst, ite_false]
        exact Rat.le_of_lt (hall t s (Ne.symm hst))
    -- Pick a witness `s0 ≠ t` to get strict inequality in the row sum.
    have hex_ne : ∃ s0 : Fin N, s0 ≠ t := by
      by_cases ht0 : t.val = 0
      · refine ⟨⟨1, by omega⟩, ?_⟩
        intro h; have hv : (1 : Nat) = t.val := congrArg Fin.val h; omega
      · refine ⟨⟨0, by omega⟩, ?_⟩
        intro h; have hv : (0 : Nat) = t.val := congrArg Fin.val h; omega
    rcases hex_ne with ⟨s0, hs0⟩
    have hstrict_s0 : dotProd (v t) (v s0) < c := hall t s0 (Ne.symm hs0)
    have hrow_lt : finSum (fun s : Fin N => dotProd (v t) (v s)) <
        finSum (fun s : Fin N => if s = t then P else c) := by
      have hdiff_pos : (0 : Rat) < finSum (fun s : Fin N =>
          (if s = t then P else c) - dotProd (v t) (v s)) := by
        have hterm_nonneg : ∀ s : Fin N, (0 : Rat) ≤ (if s = t then P else c) - dotProd (v t) (v s) :=
          fun s => rat_sub_nonneg (hbound s)
        have hs0_pos : (0 : Rat) < (if s0 = t then P else c) - dotProd (v t) (v s0) := by
          simp only [hs0, ite_false]; exact rat_sub_pos hstrict_s0
        -- Sum of nonneg terms with one strictly positive term is strictly positive
        have haux : ∀ (k : Nat) (f : Fin k → Rat) (j0 : Fin k),
            (∀ j, (0 : Rat) ≤ f j) → (0 : Rat) < f j0 → (0 : Rat) < finSum f := by
          intro k
          induction k with
          | zero => intro _ j0; exact Fin.elim0 j0
          | succ k ih =>
            intro f j0 hnn hpos
            unfold finSum
            simp only [finSumAux]
            by_cases hj : j0.val = k
            · have hjEq : j0 = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hj
              rw [hjEq] at hpos
              have hrest : (0 : Rat) ≤ finSumAux k (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) :=
                finSum_nonneg (fun j => hnn ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
              rw [Rat.add_comm]
              exact rat_add_pos_of_pos_of_nonneg hpos hrest
            · have hlt : j0.val < k := by omega
              have hih := ih (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) ⟨j0.val, hlt⟩
                (fun j => hnn ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) hpos
              unfold finSum at hih
              exact rat_add_pos_of_pos_of_nonneg hih (hnn ⟨k, Nat.lt_succ_self k⟩)
        exact haux N _ s0 hterm_nonneg hs0_pos
      rw [finSum_sub] at hdiff_pos
      exact rat_lt_of_sub_pos hdiff_pos
    -- Evaluate `finSum (fun s => if s = t then P else c) = P + (N - 1) * c = 0`.
    have hsum_val : finSum (fun s : Fin N => if s = t then P else c) = 0 := by
      have hdecomp : finSum (fun s : Fin N => if s = t then P else c) =
          finSum (fun s : Fin N => (if s = t then P - c else 0) + c) := by
        apply finSum_congr
        intro s
        by_cases hst : s = t
        · simp [hst]; grind
        · simp [hst, Rat.zero_add]
      rw [hdecomp, finSum_add, finSum_const]
      have hsingle : finSum (fun s : Fin N => if s = t then P - c else (0 : Rat)) = P - c := by
        have haux : ∀ (k : Nat) (i : Fin k) (v : Rat),
            finSum (fun j : Fin k => if j = i then v else (0 : Rat)) = v := by
          intro k
          induction k with
          | zero => intro i; exact Fin.elim0 i
          | succ k ih =>
            intro i v
            unfold finSum
            simp only [finSumAux]
            by_cases hi : i.val = k
            · have hiEq : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hi
              simp only [hiEq.symm, ite_true]
              have hz : finSumAux k (fun j => if (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) = i then v else 0) =
                  finSumAux k (fun _ => (0 : Rat)) := by
                apply finSumAux_congr
                intro j
                have hne : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) ≠ i := by
                  intro h; have hv : j.val = i.val := congrArg Fin.val h; omega
                simp [hne]
              rw [hz]
              have hz0 := finSum_zero k
              unfold finSum at hz0
              rw [hz0, Rat.zero_add]
            · have hlt : i.val < k := by omega
              have hneLast : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) ≠ i := by
                intro h; exact hi (congrArg Fin.val h).symm
              simp only [hneLast, ite_false, Rat.add_zero]
              have hcongr : finSumAux k (fun j => if (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) = i then v else 0) =
                  finSumAux k (fun j => if j = ⟨i.val, hlt⟩ then v else 0) := by
                apply finSumAux_congr
                intro j
                by_cases hj : j.val = i.val
                · have h1 : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) = i := Fin.ext hj
                  have h2 : j = ⟨i.val, hlt⟩ := Fin.ext hj
                  rw [h1, h2]; simp only [ite_true]
                · have h1 : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (k + 1)) ≠ i :=
                    fun h => hj (congrArg Fin.val h)
                  have h2 : j ≠ ⟨i.val, hlt⟩ := fun h => hj (congrArg Fin.val h)
                  simp [h1, h2]
              rw [hcongr]
              exact ih ⟨i.val, hlt⟩ v
        exact haux N t (P - c)
      rw [hsingle]
      have hNcast : (N : Rat) = ((N - 1 : Nat) : Rat) + 1 := by
        have hnat : N = (N - 1) + 1 := by omega
        conv => lhs; rw [hnat]
        rw [Rat.natCast_add]; rfl
      rw [hNcast]
      have hc_mul : ((N - 1 : Nat) : Rat) * c = -P := by
        dsimp [c]
        have hmul : ((N - 1 : Nat) : Rat) * -(P / ((N - 1 : Nat) : Rat)) =
            -(((N - 1 : Nat) : Rat) * (P / ((N - 1 : Nat) : Rat))) := by grind
        rw [hmul, rat_mul_div_cancel hN1_ne]
      grind
    rw [hsum_val] at hrow_lt
    exact hrow_lt
  -- Sum of `N ≥ 2` strictly negative row sums is strictly negative, contradicting `hsum_nonneg`.
  have htot_neg : finSum (fun t : Fin N => finSum (fun s : Fin N => dotProd (v t) (v s))) < 0 := by
    have haux : ∀ (k : Nat) (hk : 0 < k) (g : Fin k → Rat),
        (∀ j, g j < 0) → finSum g < 0 := by
      intro k
      induction k with
      | zero => intro hk; exact absurd hk (by decide)
      | succ k ih =>
        intro _ g hg
        unfold finSum
        simp only [finSumAux]
        cases k with
        | zero =>
          simp only [finSumAux, Rat.zero_add]
          exact hg ⟨0, by decide⟩
        | succ k' =>
          have ih' := ih (Nat.succ_pos k') (fun j => g ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
            (fun j => hg ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
          unfold finSum at ih'
          have hlast := hg ⟨k' + 1, Nat.lt_succ_self (k' + 1)⟩
          have hpos := rat_add_pos (rat_neg_pos_of_neg ih') (rat_neg_pos_of_neg hlast)
          apply rat_lt_of_sub_pos
          have heq : (0 : Rat) - (finSumAux (k' + 1) (fun j => g ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) +
              g ⟨k' + 1, Nat.lt_succ_self (k' + 1)⟩) =
              -finSumAux (k' + 1) (fun j => g ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) +
              -g ⟨k' + 1, Nat.lt_succ_self (k' + 1)⟩ := by grind
          rw [heq]; exact hpos
    exact haux N (by omega) _ hrow_neg
  exact Rat.not_le.mpr htot_neg hsum_nonneg

/-- **Theorem 1 (`separable_3d_mrope_axis_floor_theorem`)**:
    Universal Separable-Axis Floor Theorem for any axis-partitioned 3D `mRoPE` splitting
    `P = PT + PH + PW` rotary pairs across `(T, H, W)`, specialized to Qwen2-VL `(16, 24, 24)`
    with exact `48/64 = 3/4` floor, pigeonhole nonnegative-average guarantee, and unconditional
    Gram/Parseval Dirichlet-Welch lower bound `3/4 - 1/(4(N - 1))`. -/
theorem separable_3d_mrope_axis_floor_theorem :
    (∀ (PT PH PW : Nat)
      (cT : Fin PT → Int → Rat) (cH : Fin PH → Int → Rat) (cW : Fin PW → Int → Rat),
      (∀ k, cT k 0 = 1) → (∀ k, cH k 0 = 1) → (∀ k, cW k 0 = 1) →
      (∀ dT : Int, sep3DKernel PT PH PW cT cH cW dT 0 0 =
        (((PH + PW : Nat) : Rat) + sepAxisSum PT cT dT) / ((PT + PH + PW : Nat) : Rat)) ∧
      (∀ dH : Int, sep3DKernel PT PH PW cT cH cW 0 dH 0 =
        (((PT + PW : Nat) : Rat) + sepAxisSum PH cH dH) / ((PT + PH + PW : Nat) : Rat)) ∧
      (∀ dW : Int, sep3DKernel PT PH PW cT cH cW 0 0 dW =
        (((PT + PH : Nat) : Rat) + sepAxisSum PW cW dW) / ((PT + PH + PW : Nat) : Rat))) ∧
    (∀ (PT PH PW : Nat), 0 < PT + PH + PW →
      ∀ (cT : Fin PT → Int → Rat) (cH : Fin PH → Int → Rat) (cW : Fin PW → Int → Rat)
      (dT dH dW : Int) (M Mmin : Rat),
      (∀ k, cT k 0 = 1) → (∀ k, cH k 0 = 1) → (∀ k, cW k 0 = 1) →
      Mmin ≤ sepAxisSum PT cT dT →
      Mmin ≤ sepAxisSum PH cH dH →
      Mmin ≤ sepAxisSum PW cW dW →
      ratAbs (sep3DKernel PT PH PW cT cH cW dT 0 0) ≤ M →
      ratAbs (sep3DKernel PT PH PW cT cH cW 0 dH 0) ≤ M →
      ratAbs (sep3DKernel PT PH PW cT cH cW 0 0 dW) ≤ M →
      ((((PT + PH + PW) - min3 PT PH PW : Nat) : Rat) + Mmin) /
        ((PT + PH + PW : Nat) : Rat) ≤ M) ∧
    (∀ (cT : Fin 16 → Int → Rat) (cH : Fin 24 → Int → Rat) (cW : Fin 24 → Int → Rat),
      (∀ k, cH k 0 = 1) → (∀ k, cW k 0 = 1) →
      (∀ dT : Int, (0 : Rat) ≤ sepAxisSum 16 cT dT →
        (3 / 4 : Rat) ≤ sep3DKernel 16 24 24 cT cH cW dT 0 0 ∧
        (3 / 4 : Rat) ≤ ratAbs (sep3DKernel 16 24 24 cT cH cW dT 0 0)) ∧
      (∀ (L : Nat), 0 < L →
        (0 : Rat) ≤ finSum (fun j : Fin L => sepAxisSum 16 cT (j.val + 1)) →
        ∃ j : Fin L, (0 : Rat) ≤ sepAxisSum 16 cT (j.val + 1) ∧
          (3 / 4 : Rat) ≤ ratAbs (sep3DKernel 16 24 24 cT cH cW (j.val + 1) 0 0)) ∧
      (∀ (N d : Nat) (v : Fin N → Fin d → Rat), 2 ≤ N →
        (∀ t : Fin N, l2NormSq (v t) = 16) →
        (∀ t s : Fin N, sepAxisSum 16 cT ((t.val : Int) - (s.val : Int)) = dotProd (v t) (v s)) →
        ∃ t s : Fin N, t ≠ s ∧
          (3 / 4 : Rat) - (1 : Rat) / (4 * ((N - 1 : Nat) : Rat)) ≤
            sep3DKernel 16 24 24 cT cH cW ((t.val : Int) - (s.val : Int)) 0 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro PT PH PW cT cH cW hT0 hH0 hW0
    exact ⟨sep3DKernel_pure_T cT cH cW hH0 hW0,
           sep3DKernel_pure_H cT cH cW hT0 hW0,
           sep3DKernel_pure_W cT cH cW hT0 hH0⟩
  · intro PT PH PW hP cT cH cW dT dH dW M Mmin hT0 hH0 hW0 hMT hMH hMW hKT hKH hKW
    have hPpos : (0 : Rat) < ((PT + PH + PW : Nat) : Rat) := rat_natCast_pos hP
    have hcaseT : PT ≤ PH → PT ≤ PW →
        ((((PT + PH + PW) - min3 PT PH PW : Nat) : Rat) + Mmin) /
          ((PT + PH + PW : Nat) : Rat) ≤ M := by
      intro h1 h2
      have hmin : (PT + PH + PW) - min3 PT PH PW = PH + PW := by
        unfold min3; omega
      rw [hmin]
      have hK := sep3DKernel_pure_T cT cH cW hH0 hW0 dT
      have hle1 : (((PH + PW : Nat) : Rat) + Mmin) / ((PT + PH + PW : Nat) : Rat) ≤
          sep3DKernel PT PH PW cT cH cW dT 0 0 := by
        rw [hK]
        exact rat_div_le_div_of_nonneg_right (rat_add_le_add Rat.le_refl hMT) hPpos
      exact Rat.le_trans hle1 (Rat.le_trans (ratAbs_le_self_and_neg _).1 hKT)
    have hcaseH : PH ≤ PT → PH ≤ PW →
        ((((PT + PH + PW) - min3 PT PH PW : Nat) : Rat) + Mmin) /
          ((PT + PH + PW : Nat) : Rat) ≤ M := by
      intro h1 h2
      have hmin : (PT + PH + PW) - min3 PT PH PW = PT + PW := by
        unfold min3; omega
      rw [hmin]
      have hK := sep3DKernel_pure_H cT cH cW hT0 hW0 dH
      have hle1 : (((PT + PW : Nat) : Rat) + Mmin) / ((PT + PH + PW : Nat) : Rat) ≤
          sep3DKernel PT PH PW cT cH cW 0 dH 0 := by
        rw [hK]
        exact rat_div_le_div_of_nonneg_right (rat_add_le_add Rat.le_refl hMH) hPpos
      exact Rat.le_trans hle1 (Rat.le_trans (ratAbs_le_self_and_neg _).1 hKH)
    have hcaseW : PW ≤ PT → PW ≤ PH →
        ((((PT + PH + PW) - min3 PT PH PW : Nat) : Rat) + Mmin) /
          ((PT + PH + PW : Nat) : Rat) ≤ M := by
      intro h1 h2
      have hmin : (PT + PH + PW) - min3 PT PH PW = PT + PH := by
        unfold min3; omega
      rw [hmin]
      have hK := sep3DKernel_pure_W cT cH cW hT0 hH0 dW
      have hle1 : (((PT + PH : Nat) : Rat) + Mmin) / ((PT + PH + PW : Nat) : Rat) ≤
          sep3DKernel PT PH PW cT cH cW 0 0 dW := by
        rw [hK]
        exact rat_div_le_div_of_nonneg_right (rat_add_le_add Rat.le_refl hMW) hPpos
      exact Rat.le_trans hle1 (Rat.le_trans (ratAbs_le_self_and_neg _).1 hKW)
    by_cases h1 : PT ≤ PH
    · by_cases h2 : PT ≤ PW
      · exact hcaseT h1 h2
      · exact hcaseW (by omega) (by omega)
    · by_cases h2 : PH ≤ PW
      · exact hcaseH (by omega) h2
      · exact hcaseW (by omega) (by omega)
  · intro cT cH cW hH0 hW0
    have hqwen : ∀ dT : Int, (0 : Rat) ≤ sepAxisSum 16 cT dT →
        (3 / 4 : Rat) ≤ sep3DKernel 16 24 24 cT cH cW dT 0 0 ∧
        (3 / 4 : Rat) ≤ ratAbs (sep3DKernel 16 24 24 cT cH cW dT 0 0) := by
      intro dT hST
      have hK := sep3DKernel_pure_T cT cH cW hH0 hW0 dT
      have hle : (3 / 4 : Rat) ≤ sep3DKernel 16 24 24 cT cH cW dT 0 0 := by
        rw [hK]
        have h48 : (3 / 4 : Rat) = ((48 : Rat) + 0) / (64 : Rat) := by grind
        have hcast1 : (((24 + 24 : Nat) : Rat)) = (48 : Rat) := by decide
        have hcast2 : (((16 + 24 + 24 : Nat) : Rat)) = (64 : Rat) := by decide
        rw [hcast1, hcast2, h48]
        exact rat_div_le_div_of_nonneg_right (rat_add_le_add Rat.le_refl hST) (by decide)
      exact ⟨hle, Rat.le_trans hle (ratAbs_le_self_and_neg _).1⟩
    refine ⟨hqwen, ?_, ?_⟩
    · intro L hL hsum
      have hzero : (L : Rat) * (0 : Rat) ≤
          finSum (fun j : Fin L => sepAxisSum 16 cT (j.val + 1)) := by
        rw [Rat.mul_zero]; exact hsum
      rcases exists_ge_of_finSum_ge hL _ 0 hzero with ⟨j, hj⟩
      exact ⟨j, hj, (hqwen (j.val + 1) hj).2⟩
    · intro N d v hN hdiag hrep
      rcases gram_welch_offdiag_lower_bound hN 16 v hdiag with ⟨t, s, hne, hdot⟩
      refine ⟨t, s, hne, ?_⟩
      have hK := sep3DKernel_pure_T cT cH cW hH0 hW0 ((t.val : Int) - (s.val : Int))
      rw [hK, hrep t s]
      have hcast1 : (((24 + 24 : Nat) : Rat)) = (48 : Rat) := by decide
      have hcast2 : (((16 + 24 + 24 : Nat) : Rat)) = (64 : Rat) := by decide
      rw [hcast1, hcast2]
      have hN1_ne : ((N - 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt (rat_natCast_pos (by omega))
      have hlhs : (3 / 4 : Rat) - (1 : Rat) / (4 * ((N - 1 : Nat) : Rat)) =
          ((48 : Rat) + -((16 : Rat) / ((N - 1 : Nat) : Rat))) / (64 : Rat) := by
        have h1 : (4 * ((N - 1 : Nat) : Rat)) ≠ 0 := by
          intro h0
          cases Rat.mul_eq_zero.mp h0 with
          | inl h => exact absurd h (by decide)
          | inr h => exact hN1_ne h
        apply Eq.symm
        apply (rat_div_eq_iff (by decide : (64 : Rat) ≠ 0)).mpr
        have hmul_eq : ((48 : Rat) + -((16 : Rat) / ((N - 1 : Nat) : Rat))) * ((N - 1 : Nat) : Rat) =
            (((3 / 4 : Rat) - (1 : Rat) / (4 * ((N - 1 : Nat) : Rat))) * (64 : Rat)) *
              ((N - 1 : Nat) : Rat) := by
          have hmul1 : (((3 / 4 : Rat) - (1 : Rat) / (4 * ((N - 1 : Nat) : Rat))) * (64 : Rat)) *
              ((N - 1 : Nat) : Rat) =
              (48 : Rat) * ((N - 1 : Nat) : Rat) -
                ((1 : Rat) / (4 * ((N - 1 : Nat) : Rat))) * (4 * ((N - 1 : Nat) : Rat)) * 16 := by
            grind
          rw [hmul1, rat_div_mul_cancel h1]
          have hmul2 : ((48 : Rat) + -((16 : Rat) / ((N - 1 : Nat) : Rat))) * ((N - 1 : Nat) : Rat) =
              (48 : Rat) * ((N - 1 : Nat) : Rat) -
                ((16 : Rat) / ((N - 1 : Nat) : Rat)) * ((N - 1 : Nat) : Rat) := by grind
          rw [hmul2, rat_div_mul_cancel hN1_ne]
          grind
        have hcancel := congrArg (· * ((N - 1 : Nat) : Rat)⁻¹) hmul_eq
        rw [Rat.mul_assoc, Rat.mul_assoc, Rat.mul_inv_cancel _ hN1_ne, Rat.mul_one, Rat.mul_one] at hcancel
        exact hcancel
      rw [hlhs]
      exact rat_div_le_div_of_nonneg_right (rat_add_le_add Rat.le_refl hdot) (by decide)

/-! ### Part 2: Coupled 3D Barrier Shattering Helpers -/

theorem cosQ4_mod (m : Int) : cosQ4 (m % 4) = cosQ4 m := by
  unfold cosQ4
  rw [Int.emod_emod]

theorem sinQ4_mod (m : Int) : sinQ4 (m % 4) = sinQ4 m := by
  unfold sinQ4
  rw [Int.emod_emod]

/-- Exact angle-addition formula for quarter-turn cosine `cosQ4`. -/
theorem cosQ4_add (a b : Int) :
    cosQ4 (a + b) = cosQ4 a * cosQ4 b - sinQ4 a * sinQ4 b := by
  have ha : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  have hb : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
  have hab : (a + b) % 4 = (a % 4 + b % 4) % 4 := Int.add_emod a b 4
  unfold cosQ4 sinQ4
  rw [hab]
  rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;>
    rw [ha, hb] <;> simp <;> grind

/-- Exact 1D character sum over `ω ∈ {0, 1, 2, 3}` for `cosQ4`. -/
def sumCos4 (Δ : Int) : Rat :=
  cosQ4 (Δ * 0) + cosQ4 (Δ * 1) + cosQ4 (Δ * 2) + cosQ4 (Δ * 3)

/-- Exact 1D character sum over `ω ∈ {0, 1, 2, 3}` for `sinQ4`. -/
def sumSin4 (Δ : Int) : Rat :=
  sinQ4 (Δ * 0) + sinQ4 (Δ * 1) + sinQ4 (Δ * 2) + sinQ4 (Δ * 3)

theorem sumCos4_eval (Δ : Int) :
    sumCos4 Δ = if Δ % 4 = 0 then (4 : Rat) else (0 : Rat) := by
  have hΔ : Δ % 4 = 0 ∨ Δ % 4 = 1 ∨ Δ % 4 = 2 ∨ Δ % 4 = 3 := by omega
  unfold sumCos4 cosQ4
  have h0 : (Δ * 0) % 4 = 0 := by omega
  have h1 : (Δ * 1) % 4 = Δ % 4 := by omega
  have h2 : (Δ * 2) % 4 = (2 * (Δ % 4)) % 4 := by omega
  have h3 : (Δ * 3) % 4 = (3 * (Δ % 4)) % 4 := by omega
  rw [h0, h1, h2, h3]
  rcases hΔ with hΔ | hΔ | hΔ | hΔ <;> rw [hΔ] <;> simp <;> grind

theorem sumSin4_zero (Δ : Int) : sumSin4 Δ = 0 := by
  have hΔ : Δ % 4 = 0 ∨ Δ % 4 = 1 ∨ Δ % 4 = 2 ∨ Δ % 4 = 3 := by omega
  unfold sumSin4 sinQ4
  have h0 : (Δ * 0) % 4 = 0 := by omega
  have h1 : (Δ * 1) % 4 = Δ % 4 := by omega
  have h2 : (Δ * 2) % 4 = (2 * (Δ % 4)) % 4 := by omega
  have h3 : (Δ * 3) % 4 = (3 * (Δ % 4)) % 4 := by omega
  rw [h0, h1, h2, h3]
  rcases hΔ with hΔ | hΔ | hΔ | hΔ <;> rw [hΔ] <;> simp <;> grind

/-- Exact shift-factorization of `sumCos4`: `∑_{ω=0}^3 cosQ4(φ + Δ·ω) = cosQ4(φ) * sumCos4(Δ)`. -/
theorem sum_cosQ4_shift4 (φ Δ : Int) :
    cosQ4 (φ + Δ * 0) + cosQ4 (φ + Δ * 1) + cosQ4 (φ + Δ * 2) + cosQ4 (φ + Δ * 3) =
      cosQ4 φ * sumCos4 Δ := by
  rw [cosQ4_add, cosQ4_add, cosQ4_add, cosQ4_add]
  have hs := sumSin4_zero Δ
  unfold sumCos4 sumSin4 at *
  grind

/-- Exact 1D character sum over nonzero `ω ∈ {1, 2, 3}` for `cosQ4`. -/
def sumCos3 (Δ : Int) : Rat :=
  cosQ4 (Δ * 1) + cosQ4 (Δ * 2) + cosQ4 (Δ * 3)

/-- Exact 1D character sum over nonzero `ω ∈ {1, 2, 3}` for `sinQ4`. -/
def sumSin3 (Δ : Int) : Rat :=
  sinQ4 (Δ * 1) + sinQ4 (Δ * 2) + sinQ4 (Δ * 3)

theorem sumCos3_eval (Δ : Int) :
    sumCos3 Δ = if Δ % 4 = 0 then (3 : Rat) else (-1 : Rat) := by
  have hΔ : Δ % 4 = 0 ∨ Δ % 4 = 1 ∨ Δ % 4 = 2 ∨ Δ % 4 = 3 := by omega
  unfold sumCos3 cosQ4
  have h1 : (Δ * 1) % 4 = Δ % 4 := by omega
  have h2 : (Δ * 2) % 4 = (2 * (Δ % 4)) % 4 := by omega
  have h3 : (Δ * 3) % 4 = (3 * (Δ % 4)) % 4 := by omega
  rw [h1, h2, h3]
  rcases hΔ with hΔ | hΔ | hΔ | hΔ <;> rw [hΔ] <;> simp <;> grind

theorem sumSin3_zero (Δ : Int) : sumSin3 Δ = 0 := by
  have hΔ : Δ % 4 = 0 ∨ Δ % 4 = 1 ∨ Δ % 4 = 2 ∨ Δ % 4 = 3 := by omega
  unfold sumSin3 sinQ4
  have h1 : (Δ * 1) % 4 = Δ % 4 := by omega
  have h2 : (Δ * 2) % 4 = (2 * (Δ % 4)) % 4 := by omega
  have h3 : (Δ * 3) % 4 = (3 * (Δ % 4)) % 4 := by omega
  rw [h1, h2, h3]
  rcases hΔ with hΔ | hΔ | hΔ | hΔ <;> rw [hΔ] <;> simp <;> grind

/-- Exact shift-factorization of `sumCos3`: `∑_{ω=1}^3 cosQ4(φ + Δ·ω) = cosQ4(φ) * sumCos3(Δ)`. -/
theorem sum_cosQ4_shift3 (φ Δ : Int) :
    cosQ4 (φ + Δ * 1) + cosQ4 (φ + Δ * 2) + cosQ4 (φ + Δ * 3) =
      cosQ4 φ * sumCos3 Δ := by
  rw [cosQ4_add, cosQ4_add, cosQ4_add]
  have hs := sumSin3_zero Δ
  unfold sumCos3 sumSin3 at *
  grind

/-- Helper: split `finSum` of size `4 * m` into `m` blocks of 4. -/
theorem finSum_mul4 (m : Nat) (f : Fin (4 * m) → Rat) :
    finSum f = finSum (fun q : Fin m =>
      f ⟨4 * q.val, by omega⟩ + f ⟨4 * q.val + 1, by omega⟩ +
      f ⟨4 * q.val + 2, by omega⟩ + f ⟨4 * q.val + 3, by omega⟩) := by
  unfold finSum
  induction m with
  | zero => rfl
  | succ m ih =>
    have h4 : 4 * (m + 1) = (((4 * m + 1) + 1) + 1) + 1 := by omega
    simp only [finSumAux]
    rw [← ih (fun j => f ⟨j.val, by omega⟩)]
    have hstep : ∀ (n : Nat) (g : Fin (n + 4) → Rat),
        finSumAux (n + 4) g = finSumAux n (fun j => g ⟨j.val, by omega⟩) +
          (g ⟨n, by omega⟩ + g ⟨n + 1, by omega⟩ + g ⟨n + 2, by omega⟩ + g ⟨n + 3, by omega⟩) := by
      intro n g
      simp only [finSumAux]
      grind
    exact hstep (4 * m) f

/-- Helper: split `finSum` of size `3 * m` into `m` blocks of 3. -/
theorem finSum_mul3 (m : Nat) (f : Fin (3 * m) → Rat) :
    finSum f = finSum (fun q : Fin m =>
      f ⟨3 * q.val, by omega⟩ + f ⟨3 * q.val + 1, by omega⟩ + f ⟨3 * q.val + 2, by omega⟩) := by
  unfold finSum
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [finSumAux]
    rw [← ih (fun j => f ⟨j.val, by omega⟩)]
    have hstep : ∀ (n : Nat) (g : Fin (n + 3) → Rat),
        finSumAux (n + 3) g = finSumAux n (fun j => g ⟨j.val, by omega⟩) +
          (g ⟨n, by omega⟩ + g ⟨n + 1, by omega⟩ + g ⟨n + 2, by omega⟩) := by
      intro n g
      simp only [finSumAux]
      grind
    exact hstep (3 * m) f

/-- Exact product factorization of the 64-pair `Z_4^3` coupled 3D kernel. -/
theorem coupled3DKernelQ4_64_factor (dT dH dW : Int) :
    coupled3DKernelQ4 64 ωT64 ωH64 ωW64 dT dH dW =
      (sumCos4 dT * sumCos4 dH * sumCos4 dW) / (64 : Rat) := by
  unfold coupled3DKernelQ4
  congr 1
  -- Step 1: factor out `ωW ∈ {0, 1, 2, 3}` (64 = 4 * 16)
  rw [finSum_mul4 16 (fun k : Fin 64 => cosQ4 (dT * ωT64 k + dH * ωH64 k + dW * ωW64 k))]
  have h1 : ∀ q : Fin 16,
      cosQ4 (dT * ωT64 ⟨4 * q.val, by omega⟩ + dH * ωH64 ⟨4 * q.val, by omega⟩ + dW * ωW64 ⟨4 * q.val, by omega⟩) +
      cosQ4 (dT * ωT64 ⟨4 * q.val + 1, by omega⟩ + dH * ωH64 ⟨4 * q.val + 1, by omega⟩ + dW * ωW64 ⟨4 * q.val + 1, by omega⟩) +
      cosQ4 (dT * ωT64 ⟨4 * q.val + 2, by omega⟩ + dH * ωH64 ⟨4 * q.val + 2, by omega⟩ + dW * ωW64 ⟨4 * q.val + 2, by omega⟩) +
      cosQ4 (dT * ωT64 ⟨4 * q.val + 3, by omega⟩ + dH * ωH64 ⟨4 * q.val + 3, by omega⟩ + dW * ωW64 ⟨4 * q.val + 3, by omega⟩) =
      cosQ4 (dT * ((q.val / 4 : Nat) : Int) + dH * ((q.val % 4 : Nat) : Int)) * sumCos4 dW := by
    intro q
    have ht0 : ωT64 ⟨4 * q.val, by omega⟩ = ((q.val / 4 : Nat) : Int) := by unfold ωT64; dsimp only; congr 1; omega
    have ht1 : ωT64 ⟨4 * q.val + 1, by omega⟩ = ((q.val / 4 : Nat) : Int) := by unfold ωT64; dsimp only; congr 1; omega
    have ht2 : ωT64 ⟨4 * q.val + 2, by omega⟩ = ((q.val / 4 : Nat) : Int) := by unfold ωT64; dsimp only; congr 1; omega
    have ht3 : ωT64 ⟨4 * q.val + 3, by omega⟩ = ((q.val / 4 : Nat) : Int) := by unfold ωT64; dsimp only; congr 1; omega
    have hh0 : ωH64 ⟨4 * q.val, by omega⟩ = ((q.val % 4 : Nat) : Int) := by unfold ωH64; dsimp only; congr 1; omega
    have hh1 : ωH64 ⟨4 * q.val + 1, by omega⟩ = ((q.val % 4 : Nat) : Int) := by unfold ωH64; dsimp only; congr 1; omega
    have hh2 : ωH64 ⟨4 * q.val + 2, by omega⟩ = ((q.val % 4 : Nat) : Int) := by unfold ωH64; dsimp only; congr 1; omega
    have hh3 : ωH64 ⟨4 * q.val + 3, by omega⟩ = ((q.val % 4 : Nat) : Int) := by unfold ωH64; dsimp only; congr 1; omega
    have hw0 : ωW64 ⟨4 * q.val, by omega⟩ = 0 := by unfold ωW64; dsimp only; omega
    have hw1 : ωW64 ⟨4 * q.val + 1, by omega⟩ = 1 := by unfold ωW64; dsimp only; omega
    have hw2 : ωW64 ⟨4 * q.val + 2, by omega⟩ = 2 := by unfold ωW64; dsimp only; omega
    have hw3 : ωW64 ⟨4 * q.val + 3, by omega⟩ = 3 := by unfold ωW64; dsimp only; omega
    rw [ht0, ht1, ht2, ht3, hh0, hh1, hh2, hh3, hw0, hw1, hw2, hw3]
    exact sum_cosQ4_shift4 (dT * ((q.val / 4 : Nat) : Int) + dH * ((q.val % 4 : Nat) : Int)) dW
  rw [finSum_congr h1, finSum_mul_right]
  -- Step 2: factor out `ωH ∈ {0, 1, 2, 3}` (16 = 4 * 4)
  rw [finSum_mul4 4 (fun q : Fin 16 => cosQ4 (dT * ((q.val / 4 : Nat) : Int) + dH * ((q.val % 4 : Nat) : Int)))]
  have h2 : ∀ r : Fin 4,
      cosQ4 (dT * (((4 * r.val) / 4 : Nat) : Int) + dH * (((4 * r.val) % 4 : Nat) : Int)) +
      cosQ4 (dT * (((4 * r.val + 1) / 4 : Nat) : Int) + dH * (((4 * r.val + 1) % 4 : Nat) : Int)) +
      cosQ4 (dT * (((4 * r.val + 2) / 4 : Nat) : Int) + dH * (((4 * r.val + 2) % 4 : Nat) : Int)) +
      cosQ4 (dT * (((4 * r.val + 3) / 4 : Nat) : Int) + dH * (((4 * r.val + 3) % 4 : Nat) : Int)) =
      cosQ4 (dT * (r.val : Int)) * sumCos4 dH := by
    intro r
    have ha0 : (4 * r.val) / 4 = r.val := by omega
    have ha1 : (4 * r.val + 1) / 4 = r.val := by omega
    have ha2 : (4 * r.val + 2) / 4 = r.val := by omega
    have ha3 : (4 * r.val + 3) / 4 = r.val := by omega
    have hb0 : (4 * r.val) % 4 = 0 := by omega
    have hb1 : (4 * r.val + 1) % 4 = 1 := by omega
    have hb2 : (4 * r.val + 2) % 4 = 2 := by omega
    have hb3 : (4 * r.val + 3) % 4 = 3 := by omega
    rw [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]
    exact sum_cosQ4_shift4 (dT * (r.val : Int)) dH
  rw [finSum_congr h2, finSum_mul_right]
  -- Step 3: `finSum` over `r : Fin 4` is `sumCos4 dT`
  have h3 : finSum (fun r : Fin 4 => cosQ4 (dT * (r.val : Int))) = sumCos4 dT := by
    simp [finSum, finSumAux, sumCos4, Rat.zero_add]
  rw [h3]

/-- Exact product factorization of the 27-pair all-nonzero-axis `{1, 2, 3}^3` coupled 3D kernel. -/
theorem coupled3DKernelQ4_27_factor (dT dH dW : Int) :
    coupled3DKernelQ4 27 ωT27 ωH27 ωW27 dT dH dW =
      (sumCos3 dT * sumCos3 dH * sumCos3 dW) / (27 : Rat) := by
  unfold coupled3DKernelQ4
  congr 1
  -- Step 1: factor out `ωW ∈ {1, 2, 3}` (27 = 3 * 9)
  rw [finSum_mul3 9 (fun k : Fin 27 => cosQ4 (dT * ωT27 k + dH * ωH27 k + dW * ωW27 k))]
  have h1 : ∀ q : Fin 9,
      cosQ4 (dT * ωT27 ⟨3 * q.val, by omega⟩ + dH * ωH27 ⟨3 * q.val, by omega⟩ + dW * ωW27 ⟨3 * q.val, by omega⟩) +
      cosQ4 (dT * ωT27 ⟨3 * q.val + 1, by omega⟩ + dH * ωH27 ⟨3 * q.val + 1, by omega⟩ + dW * ωW27 ⟨3 * q.val + 1, by omega⟩) +
      cosQ4 (dT * ωT27 ⟨3 * q.val + 2, by omega⟩ + dH * ωH27 ⟨3 * q.val + 2, by omega⟩ + dW * ωW27 ⟨3 * q.val + 2, by omega⟩) =
      cosQ4 (dT * ((q.val / 3 + 1 : Nat) : Int) + dH * ((q.val % 3 + 1 : Nat) : Int)) * sumCos3 dW := by
    intro q
    have ht0 : ωT27 ⟨3 * q.val, by omega⟩ = ((q.val / 3 + 1 : Nat) : Int) := by unfold ωT27; dsimp only; congr 1; omega
    have ht1 : ωT27 ⟨3 * q.val + 1, by omega⟩ = ((q.val / 3 + 1 : Nat) : Int) := by unfold ωT27; dsimp only; congr 1; omega
    have ht2 : ωT27 ⟨3 * q.val + 2, by omega⟩ = ((q.val / 3 + 1 : Nat) : Int) := by unfold ωT27; dsimp only; congr 1; omega
    have hh0 : ωH27 ⟨3 * q.val, by omega⟩ = ((q.val % 3 + 1 : Nat) : Int) := by unfold ωH27; dsimp only; congr 1; omega
    have hh1 : ωH27 ⟨3 * q.val + 1, by omega⟩ = ((q.val % 3 + 1 : Nat) : Int) := by unfold ωH27; dsimp only; congr 1; omega
    have hh2 : ωH27 ⟨3 * q.val + 2, by omega⟩ = ((q.val % 3 + 1 : Nat) : Int) := by unfold ωH27; dsimp only; congr 1; omega
    have hw0 : ωW27 ⟨3 * q.val, by omega⟩ = 1 := by unfold ωW27; dsimp only; omega
    have hw1 : ωW27 ⟨3 * q.val + 1, by omega⟩ = 2 := by unfold ωW27; dsimp only; omega
    have hw2 : ωW27 ⟨3 * q.val + 2, by omega⟩ = 3 := by unfold ωW27; dsimp only; omega
    rw [ht0, ht1, ht2, hh0, hh1, hh2, hw0, hw1, hw2]
    exact sum_cosQ4_shift3 (dT * ((q.val / 3 + 1 : Nat) : Int) + dH * ((q.val % 3 + 1 : Nat) : Int)) dW
  rw [finSum_congr h1, finSum_mul_right]
  -- Step 2: factor out `ωH ∈ {1, 2, 3}` (9 = 3 * 3)
  rw [finSum_mul3 3 (fun q : Fin 9 =>
    cosQ4 (dT * ((q.val / 3 + 1 : Nat) : Int) + dH * ((q.val % 3 + 1 : Nat) : Int)))]
  have h2 : ∀ r : Fin 3,
      cosQ4 (dT * (((3 * r.val) / 3 + 1 : Nat) : Int) + dH * (((3 * r.val) % 3 + 1 : Nat) : Int)) +
      cosQ4 (dT * (((3 * r.val + 1) / 3 + 1 : Nat) : Int) + dH * (((3 * r.val + 1) % 3 + 1 : Nat) : Int)) +
      cosQ4 (dT * (((3 * r.val + 2) / 3 + 1 : Nat) : Int) + dH * (((3 * r.val + 2) % 3 + 1 : Nat) : Int)) =
      cosQ4 (dT * ((r.val + 1 : Nat) : Int)) * sumCos3 dH := by
    intro r
    have ha0 : (3 * r.val) / 3 + 1 = r.val + 1 := by omega
    have ha1 : (3 * r.val + 1) / 3 + 1 = r.val + 1 := by omega
    have ha2 : (3 * r.val + 2) / 3 + 1 = r.val + 1 := by omega
    have hb0 : (3 * r.val) % 3 + 1 = 1 := by omega
    have hb1 : (3 * r.val + 1) % 3 + 1 = 2 := by omega
    have hb2 : (3 * r.val + 2) % 3 + 1 = 3 := by omega
    rw [ha0, ha1, ha2, hb0, hb1, hb2]
    exact sum_cosQ4_shift3 (dT * ((r.val + 1 : Nat) : Int)) dH
  rw [finSum_congr h2, finSum_mul_right]
  -- Step 3: `finSum` over `r : Fin 3` is `sumCos3 dT`
  have h3 : finSum (fun r : Fin 3 => cosQ4 (dT * ((r.val + 1 : Nat) : Int))) = sumCos3 dT := by
    simp [finSum, finSumAux, sumCos3, Rat.zero_add]
  rw [h3]

/-- **Theorem 2 (`coupled_3d_mrope_shatters_separable_floor`)**:
    Proves that Coupled 3D rotary phases completely eliminate the separable `(P_H + P_W)/P`
    additive axis floor, certifying:
    (1) general coupled pure-axis bound without any constant floor;
    (2) exact 64-pair `Z_4^3` coupled witness with `K(0,0,0) = 1` and `K(dT, dH, dW) = 0 < 1/2 < 3/4`
        for every non-period offset (all 63 nonzero offsets in `{0, 1, 2, 3}^3`, zero mean-square sidelobe);
    (3) exact 27-pair all-nonzero-axis `{1, 2, 3}^3` coupled witness where EVERY pair actively
        participates in all 3 axes (`ωT, ωH, ωW ≠ 0`), `K(0,0,0) = 1`, and
        `|K(dT, dH, dW)| ≤ 1/3 < 1/2 < 3/4` (squared sidelobe `≤ 1/9`) on every non-period offset. -/
theorem coupled_3d_mrope_shatters_separable_floor :
    (∀ (P : Nat), 0 < P → ∀ (c : Fin P → Int → Int → Int → Rat) (dT : Int) (B : Rat),
      (0 : Rat) ≤ B →
      (∀ k : Fin P, ratAbs (c k dT 0 0) ≤ B) →
      ratAbs (coupled3DGeneral P c dT 0 0) ≤ B) ∧
    (coupled3DKernelQ4 64 ωT64 ωH64 ωW64 0 0 0 = 1 ∧
      (∀ dT dH dW : Int, ¬ (dT % 4 = 0 ∧ dH % 4 = 0 ∧ dW % 4 = 0) →
        coupled3DKernelQ4 64 ωT64 ωH64 ωW64 dT dH dW = 0 ∧
        ratAbs (coupled3DKernelQ4 64 ωT64 ωH64 ωW64 dT dH dW) < (1 / 2 : Rat) ∧
        ratAbs (coupled3DKernelQ4 64 ωT64 ωH64 ωW64 dT dH dW) < (3 / 4 : Rat)) ∧
      (∀ ε : Rat, (0 : Rat) < ε → ∀ dT : Int, dT % 4 ≠ 0 →
        ratAbs (coupled3DKernelQ4 64 ωT64 ωH64 ωW64 dT 0 0) < ε)) ∧
    ((∀ k : Fin 27, ωT27 k ≠ 0 ∧ ωH27 k ≠ 0 ∧ ωW27 k ≠ 0) ∧
      coupled3DKernelQ4 27 ωT27 ωH27 ωW27 0 0 0 = 1 ∧
      (∀ dT dH dW : Int, ¬ (dT % 4 = 0 ∧ dH % 4 = 0 ∧ dW % 4 = 0) →
        ratAbs (coupled3DKernelQ4 27 ωT27 ωH27 ωW27 dT dH dW) ≤ (1 / 3 : Rat) ∧
        ratAbs (coupled3DKernelQ4 27 ωT27 ωH27 ωW27 dT dH dW) < (1 / 2 : Rat) ∧
        ratAbs (coupled3DKernelQ4 27 ωT27 ωH27 ωW27 dT dH dW) < (3 / 4 : Rat) ∧
        coupled3DKernelQ4 27 ωT27 ωH27 ωW27 dT dH dW *
          coupled3DKernelQ4 27 ωT27 ωH27 ωW27 dT dH dW ≤ (1 / 9 : Rat))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: general coupled bound (zero constant floor)
    intro P hP c dT B hB hbound
    unfold coupled3DGeneral
    have hPpos : (0 : Rat) < (P : Rat) := rat_natCast_pos hP
    apply ratAbs_le_iff.mpr
    have hupper : finSum (fun k => c k dT 0 0) ≤ B * (P : Rat) := by
      have h1 : finSum (fun k => c k dT 0 0) ≤ finSum (fun _ : Fin P => B) :=
        finSum_le_finSum (fun k => (ratAbs_le_iff.mp (hbound k)).2)
      rw [finSum_const, Rat.mul_comm] at h1
      exact h1
    have hlower : (-B) * (P : Rat) ≤ finSum (fun k => c k dT 0 0) := by
      have h1 : finSum (fun _ : Fin P => -B) ≤ finSum (fun k => c k dT 0 0) :=
        finSum_le_finSum (fun k => (ratAbs_le_iff.mp (hbound k)).1)
      rw [finSum_const, Rat.mul_comm] at h1
      exact h1
    exact ⟨rat_le_div_of_mul_le hPpos hlower, rat_div_le_of_mul_le hPpos hupper⟩
  · -- Part 2: 64-pair Z_4^3 coupled witness
    have h0 : coupled3DKernelQ4 64 ωT64 ωH64 ωW64 0 0 0 = 1 := by
      rw [coupled3DKernelQ4_64_factor, sumCos4_eval]
      simp; grind
    have hnz : ∀ dT dH dW : Int, ¬ (dT % 4 = 0 ∧ dH % 4 = 0 ∧ dW % 4 = 0) →
        coupled3DKernelQ4 64 ωT64 ωH64 ωW64 dT dH dW = 0 := by
      intro dT dH dW hne
      rw [coupled3DKernelQ4_64_factor, sumCos4_eval, sumCos4_eval, sumCos4_eval]
      by_cases hT : dT % 4 = 0
      · by_cases hH : dH % 4 = 0
        · have hW : dW % 4 ≠ 0 := fun hW => hne ⟨hT, hH, hW⟩
          simp [hT, hH, hW]; grind
        · simp [hT, hH]; grind
      · simp [hT]; grind
    refine ⟨h0, ?_, ?_⟩
    · intro dT dH dW hne
      rw [hnz dT dH dW hne]
      refine ⟨rfl, ?_, ?_⟩
      · rw [ratAbs_of_nonneg Rat.le_refl]; exact rat_div_pos (by decide) (by decide)
      · rw [ratAbs_of_nonneg Rat.le_refl]; exact rat_div_pos (by decide) (by decide)
    · intro ε hε dT hT
      have hne : ¬ (dT % 4 = 0 ∧ (0 : Int) % 4 = 0 ∧ (0 : Int) % 4 = 0) :=
        fun h => hT h.1
      rw [hnz dT 0 0 hne, ratAbs_of_nonneg Rat.le_refl]
      exact hε
  · -- Part 3: 27-pair all-nonzero-axis {1, 2, 3}^3 coupled witness
    have hall_nz : ∀ k : Fin 27, ωT27 k ≠ 0 ∧ ωH27 k ≠ 0 ∧ ωW27 k ≠ 0 := by
      intro k
      unfold ωT27 ωH27 ωW27
      omega
    have h0 : coupled3DKernelQ4 27 ωT27 ωH27 ωW27 0 0 0 = 1 := by
      rw [coupled3DKernelQ4_27_factor, sumCos3_eval]
      simp; grind
    -- Helper: any `x` with `-1/3 ≤ x ≤ 1/3` satisfies all 4 bounds.
    have hbounds : ∀ x : Rat, (-(1 / 3 : Rat) ≤ x ∧ x ≤ (1 / 3 : Rat)) →
        ratAbs x ≤ (1 / 3 : Rat) ∧ ratAbs x < (1 / 2 : Rat) ∧
        ratAbs x < (3 / 4 : Rat) ∧ x * x ≤ (1 / 9 : Rat) := by
      intro x hx
      have habs : ratAbs x ≤ (1 / 3 : Rat) := ratAbs_le_iff.mpr hx
      have h13_12 : (1 / 3 : Rat) < (1 / 2 : Rat) := by
        apply rat_lt_of_mul_pos_right (by decide : (0 : Rat) < 6)
        have hl : (1 / 3 : Rat) * 6 = 2 := by grind
        have hr : (1 / 2 : Rat) * 6 = 3 := by grind
        rw [hl, hr]; decide
      have h12_34 : (1 / 2 : Rat) < (3 / 4 : Rat) := by
        apply rat_lt_of_mul_pos_right (by decide : (0 : Rat) < 4)
        have hl : (1 / 2 : Rat) * 4 = 2 := by grind
        have hr : (3 / 4 : Rat) * 4 = 3 := by grind
        rw [hl, hr]; decide
      have hsq : x * x ≤ (1 / 9 : Rat) := by
        have h1 : ratAbs x * ratAbs x ≤ (1 / 3 : Rat) * (1 / 3 : Rat) := by
          have ha := rat_mul_le_mul_of_nonneg_right habs (ratAbs_nonneg x)
          have hb := rat_mul_le_mul_of_nonneg_left habs
            (Rat.le_of_lt (rat_div_pos (by decide : (0 : Rat) < 1) (by decide : (0 : Rat) < 3)))
          exact Rat.le_trans ha hb
        have hsq_eq : ratAbs x * ratAbs x = x * x := by
          unfold ratAbs; split <;> grind
        have h9 : (1 / 3 : Rat) * (1 / 3 : Rat) = (1 / 9 : Rat) := by grind
        rw [hsq_eq, h9] at h1
        exact h1
      exact ⟨habs, rat_lt_of_le_of_lt habs h13_12,
             rat_lt_trans (rat_lt_of_le_of_lt habs h13_12) h12_34, hsq⟩
    have hbox_m13 : (-(1 / 3 : Rat) ≤ (-(1 / 3 : Rat)) ∧ (-(1 / 3 : Rat)) ≤ (1 / 3 : Rat)) := by
      refine ⟨Rat.le_refl, ?_⟩
      apply rat_le_of_sub_nonneg
      have h : (1 / 3 : Rat) - -(1 / 3 : Rat) = (2 : Rat) / 3 := by grind
      rw [h]; exact Rat.le_of_lt (rat_div_pos (by decide) (by decide))
    have hbox_19 : (-(1 / 3 : Rat) ≤ (1 / 9 : Rat) ∧ (1 / 9 : Rat) ≤ (1 / 3 : Rat)) := by
      constructor
      · apply rat_le_of_sub_nonneg
        have h : (1 / 9 : Rat) - -(1 / 3 : Rat) = (4 : Rat) / 9 := by grind
        rw [h]; exact Rat.le_of_lt (rat_div_pos (by decide) (by decide))
      · apply rat_le_of_sub_nonneg
        have h : (1 / 3 : Rat) - (1 / 9 : Rat) = (2 : Rat) / 9 := by grind
        rw [h]; exact Rat.le_of_lt (rat_div_pos (by decide) (by decide))
    have hbox_m127 : (-(1 / 3 : Rat) ≤ (-(1 / 27 : Rat)) ∧ (-(1 / 27 : Rat)) ≤ (1 / 3 : Rat)) := by
      constructor
      · apply rat_le_of_sub_nonneg
        have h : -(1 / 27 : Rat) - -(1 / 3 : Rat) = (8 : Rat) / 27 := by grind
        rw [h]; exact Rat.le_of_lt (rat_div_pos (by decide) (by decide))
      · apply rat_le_of_sub_nonneg
        have h : (1 / 3 : Rat) - -(1 / 27 : Rat) = (10 : Rat) / 27 := by grind
        rw [h]; exact Rat.le_of_lt (rat_div_pos (by decide) (by decide))
    refine ⟨hall_nz, h0, ?_⟩
    intro dT dH dW hne
    rw [coupled3DKernelQ4_27_factor, sumCos3_eval, sumCos3_eval, sumCos3_eval]
    by_cases hT : dT % 4 = 0 <;> by_cases hH : dH % 4 = 0 <;> by_cases hW : dW % 4 = 0
    · exact absurd ⟨hT, hH, hW⟩ hne
    · simp only [hT, hH, hW, ite_true, ite_false]
      have heq : (3 : Rat) * 3 * -1 / 27 = -(1 / 3 : Rat) := by grind
      rw [heq]; exact hbounds _ hbox_m13
    · simp only [hT, hH, hW, ite_true, ite_false]
      have heq : (3 : Rat) * -1 * 3 / 27 = -(1 / 3 : Rat) := by grind
      rw [heq]; exact hbounds _ hbox_m13
    · simp only [hT, hH, hW, ite_true, ite_false]
      have heq : (3 : Rat) * -1 * -1 / 27 = (1 / 9 : Rat) := by grind
      rw [heq]; exact hbounds _ hbox_19
    · simp only [hT, hH, hW, ite_true, ite_false]
      have heq : (-1 : Rat) * 3 * 3 / 27 = -(1 / 3 : Rat) := by grind
      rw [heq]; exact hbounds _ hbox_m13
    · simp only [hT, hH, hW, ite_true, ite_false]
      have heq : (-1 : Rat) * 3 * -1 / 27 = (1 / 9 : Rat) := by grind
      rw [heq]; exact hbounds _ hbox_19
    · simp only [hT, hH, hW, ite_true, ite_false]
      have heq : (-1 : Rat) * -1 * 3 / 27 = (1 / 9 : Rat) := by grind
      rw [heq]; exact hbounds _ hbox_19
    · simp only [hT, hH, hW, ite_false]
      have heq : (-1 : Rat) * -1 * -1 / 27 = -(1 / 27 : Rat) := by grind
      rw [heq]; exact hbounds _ hbox_m127

end Mrope3dCoprime
