import Std
import CombInequalities.CombDefs

/-!
# Kernel-Checked Theorems Discovered via RX 7900 XTX GPU Mining

All theorems here are proved completely inside Lean 4.34.1 using standard
constructive/classical axioms only (`propext`, `Classical.choice`, `Quot.sound`),
with zero `sorry` and zero `native_decide`:

1. `albertson_le_orderedIndP3`:
   For every finite simple graph `G`, `albertson G ≤ orderedIndP3 G` (`= 2 * indP3 G`).
2. `sidon_sym_defect_eq` and `sidon_two_runs_eq`:
   For every finite Sidon set `A`, `symDefect A + 4 = 2 * |A|` and `2 * runs A = |A| + isolated A`.
3. `des_add_incSubseq_le_length` (and `perm_des_add_incSubseq_le`):
   For every list `xs` and every strictly increasing sublist `sub`,
   `desList xs + sub.length ≤ xs.length` (with equality for `231`-avoiding permutations).
4. `avoids321_wexc_iff_lrmax` and `avoids321_disp_bound`:
   For every `321`-avoiding permutation `p`, weak excedances coincide with
   left-to-right maxima, and every element's Chebyshev displacement `|p(i) - i|`
   is bounded above by the length of an explicit strictly increasing subsequence.
5-18. Rounds 2-9 discoveries & structural bounds across graphs, additive sets, and
   stack/pop-stack permutations (`avoids231_two_inv_le_disp2_add_des`, `triangleFree_edgeCount_le_matching`,
   `c4Free_minDeg_le_matching`, `westSortList_inv_le_pat231`, `popSortList_inv_add_des_le_inv`,
   `connected_diam_add_one_le_three_mul_dom`, `connected_diam_le_three_mul_indNu`,
   `minDeg_le_dom_of_c4free_triangleFree`, `diam_add_minDeg_le`, `stackDes_le_peaksCnt`,
   `westSortList_preserves_incSubseq`, `popSortList_preserves_incSubseq`,
   `connected_diam_le_indP4_add_two`, `two_card_add_symDefect_le_diffset_add_one`).
19-23. Round 10 solutions to open permutation conjectures (`stackInv_le_popInv`,
   `avoids321_three_stack2Inv_le_pat231`) plus structural theorems backing zero-token
   novelty certification (`indep_add_dom_le_of_noIsolates`, `two_mul_dom_le_of_noIsolates`,
   `clique_le_maxDeg_of_connected_notComplete`, `connected_diam_add_one_le_two_mul_alpha`,
   `connected_diam_add_clique_le`, `intDilateSum2Card_le_intSum3Card`,
   `intDilateDiff2Card_le_intSum2Diff1Card`, `three_diffset_le_two_sum2Diff1_add_one`,
   `symDefectPrefix_add_four_le_two_card`, `two_card_le_intRestSumCard_add_three`,
   `PermFin.erdos_szekeres`, `PermFin.involution_incSubseq_le_cycCnt`,
   `PermFin.involution_erdos_szekeres_cyc`, `PermFin.avoids321_cycCnt_le_lis`).
-/

namespace CombMining

-- ============================================================================
-- Theorem 1: Albertson Irregularity <= 2 * Induced P3
-- ============================================================================

namespace SimpleGraphFin

def wedges {n : Nat} (G : SimpleGraphFin n) (u v : Fin n) : Nat :=
  (List.finRange n).countP (fun w => G.adj u w && !G.adj v w && decide (w ≠ v))

def commonNbrs {n : Nat} (G : SimpleGraphFin n) (u v : Fin n) : Nat :=
  (List.finRange n).countP (fun w => G.adj u w && G.adj v w)

theorem commonNbrs_symm {n : Nat} (G : SimpleGraphFin n) (u v : Fin n) :
    G.commonNbrs u v = G.commonNbrs v u := by
  unfold commonNbrs
  rw [countP_eq_sumNat, countP_eq_sumNat]
  apply sumNat_congr
  intro w _
  rw [G.symm u w, G.symm v w, Bool.and_comm]

theorem deg_eq_one_add_common_add_wedges {n : Nat} (G : SimpleGraphFin n)
    (u v : Fin n) (huv : G.adj u v = true) :
    G.deg u = 1 + G.commonNbrs u v + G.wedges u v := by
  have hind : sumNat (List.finRange n) (fun w => if w = v then 1 else 0) = 1 :=
    sumNat_eq_indicator_one (List.finRange n) (List.nodup_finRange n) v (List.mem_finRange v)
  rw [show 1 + G.commonNbrs u v + G.wedges u v =
      sumNat (List.finRange n) (fun w => if w = v then 1 else 0) + G.commonNbrs u v + G.wedges u v
      by rw [hind]]
  unfold deg commonNbrs wedges
  rw [countP_eq_sumNat, countP_eq_sumNat, countP_eq_sumNat]
  rw [← sumNat_add, ← sumNat_add]
  apply sumNat_congr
  intro w _
  cases huw : G.adj u w <;> cases hvw : G.adj v w <;> by_cases hwv : w = v
  · subst hwv; simp [huv] at huw
  · simp [hwv]
  · subst hwv; simp [G.loopless] at hvw
  · simp [hwv]
  · subst hwv; simp
  · simp [hwv]
  · subst hwv; simp [G.loopless] at hvw
  · simp [hwv]

theorem edge_abs_deg_diff_le_wedges {n : Nat} (G : SimpleGraphFin n)
    (u v : Fin n) (huv : G.adj u v = true) :
    natAbsDiff (G.deg u) (G.deg v) ≤ G.wedges u v + G.wedges v u := by
  have hu := G.deg_eq_one_add_common_add_wedges u v huv
  have hv := G.deg_eq_one_add_common_add_wedges v u (by rw [G.symm]; exact huv)
  rw [hu, hv, G.commonNbrs_symm v u]
  rw [Nat.add_assoc 1 (G.commonNbrs u v) (G.wedges u v),
      Nat.add_assoc 1 (G.commonNbrs u v) (G.wedges v u)]
  rw [natAbsDiff_add_cancel, natAbsDiff_add_cancel]
  exact natAbsDiff_le_add (G.wedges u v) (G.wedges v u)

private theorem two_mul_sumNat_fin_lt {n : Nat} (f : Fin n → Fin n → Nat)
    (hsymm : ∀ u v, f u v = f v u) (hdiag : ∀ u, f u u = 0) :
    2 * sumNat (List.finRange n) (fun u =>
          sumNat (List.finRange n) (fun v => if u.val < v.val then f u v else 0)) =
        sumNat (List.finRange n) (fun u =>
          sumNat (List.finRange n) (fun v => f u v)) := by
  have hpart :
      sumNat (List.finRange n) (fun u => sumNat (List.finRange n) (fun v => f u v)) =
      sumNat (List.finRange n) (fun u =>
        sumNat (List.finRange n) (fun v => if u.val < v.val then f u v else 0)) +
      sumNat (List.finRange n) (fun u =>
        sumNat (List.finRange n) (fun v => if v.val < u.val then f u v else 0)) := by
    rw [← sumNat_add]
    apply sumNat_congr
    intro u _
    rw [← sumNat_add]
    apply sumNat_congr
    intro v _
    rcases Nat.lt_trichotomy u.val v.val with hlt | heq | hgt
    · have hngt : ¬ (v.val < u.val) := by omega
      simp [hlt, hngt]
    · have huv : u = v := Fin.ext heq
      subst huv
      simp [hdiag u]
    · have hnlt : ¬ (u.val < v.val) := by omega
      simp [hnlt, hgt]
  have hswap :
      sumNat (List.finRange n) (fun u =>
        sumNat (List.finRange n) (fun v => if v.val < u.val then f u v else 0)) =
      sumNat (List.finRange n) (fun u =>
        sumNat (List.finRange n) (fun v => if u.val < v.val then f u v else 0)) := by
    rw [sumNat_swap]
    apply sumNat_congr
    intro v _
    apply sumNat_congr
    intro u _
    split
    · rw [hsymm]
    · rfl
  rw [hswap] at hpart
  omega

theorem albertson_le_orderedIndP3 {n : Nat} (G : SimpleGraphFin n) :
    G.albertson ≤ G.orderedIndP3 := by
  let f : Fin n → Fin n → Nat :=
    fun u v => if G.adj u v = true then natAbsDiff (G.deg u) (G.deg v) else 0
  have hsymm : ∀ u v, f u v = f v u := by
    intro u v
    simp only [f, G.symm u v, natAbsDiff_symm]
  have hdiag : ∀ u, f u u = 0 := by
    intro u
    simp [f, G.loopless]
  have halb :
      G.albertson = sumNat (List.finRange n) (fun u =>
        sumNat (List.finRange n) (fun v => if u.val < v.val then f u v else 0)) := by
    unfold albertson
    apply sumNat_congr
    intro u _
    apply sumNat_congr
    intro v _
    simp only [f]
    by_cases hlt : u.val < v.val <;> by_cases hadj : G.adj u v = true <;> simp [hlt, hadj]
  have h2alb :
      2 * G.albertson = sumNat (List.finRange n) (fun u =>
        sumNat (List.finRange n) (fun v => f u v)) := by
    rw [halb]
    exact two_mul_sumNat_fin_lt f hsymm hdiag
  have hbound :
      sumNat (List.finRange n) (fun u => sumNat (List.finRange n) (fun v => f u v)) ≤
      sumNat (List.finRange n) (fun u =>
        sumNat (List.finRange n) (fun v =>
          (if G.adj u v = true then G.wedges u v else 0) +
          (if G.adj u v = true then G.wedges v u else 0))) := by
    apply sumNat_mono
    intro u _
    apply sumNat_mono
    intro v _
    simp only [f]
    by_cases hadj : G.adj u v = true
    · simp only [hadj, ite_true]
      exact G.edge_abs_deg_diff_le_wedges u v hadj
    · simp [hadj]
  have hord :
      G.orderedIndP3 = sumNat (List.finRange n) (fun u =>
        sumNat (List.finRange n) (fun v => if G.adj u v = true then G.wedges u v else 0)) := by
    unfold orderedIndP3 wedges
    apply sumNat_congr
    intro u _
    apply sumNat_congr
    intro v _
    rw [countP_eq_sumNat]
    by_cases hadj : G.adj u v = true
    · simp only [hadj, ite_true]
      apply sumNat_congr
      intro w _
      cases huw : G.adj u w <;> cases hvw : G.adj v w <;> by_cases hwv : w = v <;>
        simp [hwv]
    · have hadjf : G.adj u v = false := Bool.eq_false_iff.mpr hadj
      simp only [hadjf, Bool.false_eq_true, false_and, ↓reduceIte]
      clear h2alb hbound halb hdiag hsymm hadj hadjf
      induction (List.finRange n) with
      | nil => rfl
      | cons w ws ih => simp [sumNat, ih]
  have hrhs_split :
      sumNat (List.finRange n) (fun u =>
        sumNat (List.finRange n) (fun v =>
          (if G.adj u v = true then G.wedges u v else 0) +
          (if G.adj u v = true then G.wedges v u else 0))) =
      2 * G.orderedIndP3 := by
    have hsplit : ∀ u,
        sumNat (List.finRange n) (fun v =>
          (if G.adj u v = true then G.wedges u v else 0) +
          (if G.adj u v = true then G.wedges v u else 0)) =
        sumNat (List.finRange n) (fun v => if G.adj u v = true then G.wedges u v else 0) +
        sumNat (List.finRange n) (fun v => if G.adj u v = true then G.wedges v u else 0) :=
      fun u => sumNat_add (List.finRange n) _ _
    rw [sumNat_congr (List.finRange n) _ _ (fun u _ => hsplit u)]
    rw [sumNat_add]
    have hswap :
        sumNat (List.finRange n) (fun u =>
          sumNat (List.finRange n) (fun v => if G.adj u v = true then G.wedges v u else 0)) =
        sumNat (List.finRange n) (fun u =>
          sumNat (List.finRange n) (fun v => if G.adj u v = true then G.wedges u v else 0)) := by
      rw [sumNat_swap]
      apply sumNat_congr
      intro v _
      apply sumNat_congr
      intro u _
      rw [G.symm]
    rw [hswap, ← hord]
    omega
  omega

end SimpleGraphFin

-- ============================================================================
-- Theorem 2: Sidon Symmetry Defect & Run-Length Laws
-- ============================================================================

private theorem sumNat_range_rev (m : Nat) (g : Nat → Nat) :
    sumNat (List.range (m + 1)) (fun k => g (m - k)) =
    sumNat (List.range (m + 1)) g := by
  induction m generalizing g with
  | zero => simp [sumNat]
  | succ m ih =>
    rw [List.range_succ, sumNat_append]
    simp only [sumNat, Nat.sub_self, Nat.add_zero]
    have hshift :
        sumNat (List.range (m + 1)) (fun k => g (m + 1 - k)) =
        sumNat (List.range (m + 1)) (fun k => (fun t => g (t + 1)) (m - k)) := by
      apply sumNat_congr
      intro k hk
      rw [List.mem_range] at hk
      have : m + 1 - k = m - k + 1 := by omega
      rw [this]
    rw [hshift, ih (fun t => g (t + 1))]
    have hrhs : sumNat (List.range (m + 1) ++ [m + 1]) g =
        g 0 + sumNat (List.range (m + 1)) (fun t => g (t + 1)) := by
      rw [← List.range_succ, List.range_succ_eq_map, sumNat, sumNat_map]
    rw [hrhs]
    omega

theorem sidon_sym_defect_eq (A : Nat → Bool) (mn mx : Nat)
    (hsid : IsSidonPred A) (hlt : mn < mx)
    (hmn : A mn = true) (hmx : A mx = true) :
    symDefectInterval A mn mx + 4 = 2 * cardInterval A mn mx := by
  let m := mx - mn
  have hm_pos : 0 < m := by omega
  have hno_mid : ∀ k ≤ m, A (mn + k) = true → A (mx - k) = true → k = 0 ∨ k = m := by
    intro k hk ha hb
    have hsum : (mn + k) + (mx - k) = mn + mx := by omega
    have heq := hsid (mn + k) (mx - k) mn mx ha hb hmn hmx hsum
    rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
    · left; omega
    · right; omega
  have hpoint : ∀ k ∈ List.range (m + 1),
      (if A (mn + k) != A (mx - k) then 1 else 0) +
      (if k = 0 then 2 else 0) +
      (if k = m then 2 else 0) =
      (if A (mn + k) then 1 else 0) + (if A (mx - k) then 1 else 0) := by
    intro k hk
    rw [List.mem_range] at hk
    by_cases hk0 : k = 0
    · subst hk0
      have hkm : (0 : Nat) ≠ m := by omega
      have hmx0 : mx - 0 = mx := by omega
      simp [hkm, hmn, hmx, hmx0]
    · by_cases hkm : k = m
      · subst hkm
        have hmnm : mn + m = mx := by omega
        have hmxm : mx - m = mn := by omega
        simp [hk0, hmnm, hmxm, hmn, hmx]
      · have hnotboth : ¬ (A (mn + k) = true ∧ A (mx - k) = true) := by
          intro ⟨ha, hb⟩
          rcases hno_mid k (by omega) ha hb with rfl | rfl <;> contradiction
        cases ha : A (mn + k) <;> cases hb : A (mx - k)
        · simp [hk0, hkm]
        · simp [hk0, hkm]
        · simp [hk0, hkm]
        · exact False.elim (hnotboth ⟨ha, hb⟩)
  have hsum_eq :
      symDefectInterval A mn mx +
      sumNat (List.range (m + 1)) (fun k => if k = 0 then 2 else 0) +
      sumNat (List.range (m + 1)) (fun k => if k = m then 2 else 0) =
      cardInterval A mn mx + sumNat (List.range (m + 1)) (fun k => if A (mx - k) then 1 else 0) := by
    unfold symDefectInterval cardInterval
    dsimp [m]
    rw [← sumNat_add, ← sumNat_add, ← sumNat_add]
    exact sumNat_congr (List.range (m + 1)) _ _ hpoint
  have h0 : sumNat (List.range (m + 1)) (fun k => if k = 0 then 2 else 0) = 2 := by
    have hind0 := sumNat_eq_indicator_one (List.range (m + 1)) List.nodup_range 0 (by simp)
    have h2 := sumNat_const_mul 2 (List.range (m + 1)) (fun k => if k = 0 then 1 else 0)
    rw [hind0, Nat.mul_one] at h2
    calc sumNat (List.range (m + 1)) (fun k => if k = 0 then 2 else 0)
        = sumNat (List.range (m + 1)) (fun k => 2 * if k = 0 then 1 else 0) := by
          apply sumNat_congr; intro k _; split <;> simp
      _ = 2 := h2.symm
  have hm : sumNat (List.range (m + 1)) (fun k => if k = m then 2 else 0) = 2 := by
    have hindm := sumNat_eq_indicator_one (List.range (m + 1)) List.nodup_range m (by simp)
    have h2 := sumNat_const_mul 2 (List.range (m + 1)) (fun k => if k = m then 1 else 0)
    rw [hindm, Nat.mul_one] at h2
    calc sumNat (List.range (m + 1)) (fun k => if k = m then 2 else 0)
        = sumNat (List.range (m + 1)) (fun k => 2 * if k = m then 1 else 0) := by
          apply sumNat_congr; intro k _; split <;> simp
      _ = 2 := h2.symm
  have hrev :
      sumNat (List.range (m + 1)) (fun k => if A (mx - k) then 1 else 0) =
      cardInterval A mn mx := by
    have hmxk : ∀ k ∈ List.range (m + 1), mx - k = mn + (m - k) := by
      intro k hk
      rw [List.mem_range] at hk
      omega
    rw [sumNat_congr (List.range (m + 1)) _ (fun k => if A (mn + (m - k)) then 1 else 0) (fun k hk => by rw [hmxk k hk])]
    exact sumNat_range_rev m (fun t => if A (mn + t) then 1 else 0)
  rw [h0, hm, hrev] at hsum_eq
  omega

theorem sidon_no_three_consec (A : Nat → Bool) (hsid : IsSidonPred A) (x : Nat) :
    ¬ (A x = true ∧ A (x + 1) = true ∧ A (x + 2) = true) := by
  intro ⟨h0, h1, h2⟩
  have heq := hsid (x + 1) (x + 1) x (x + 2) h1 h1 h0 h2 (by omega)
  rcases heq with ⟨ha, _⟩ | ⟨ha, _⟩ <;> omega

theorem sidon_two_runs_eq (A : Nat → Bool) (N : Nat)
    (hsid : IsSidonPred A) (hbound : ∀ x ≥ N, A x = false) :
    2 * runsPrefix A N = cardPrefix A N + isolatedPrefix A N := by
  -- First show sum of run starts equals sum of run ends on [0..N-1]
  have hstart_end :
      runsPrefix A N = sumNat (List.range N) (fun x => if isRunEnd A x then 1 else 0) := by
    unfold runsPrefix
    have h1 :
        sumNat (List.range N) (fun x => if isRunStart A x then 1 else 0) +
        sumNat (List.range N) (fun x => if (if x = 0 then false else A (x - 1) && A x) then 1 else 0) =
        cardPrefix A N := by
      rw [← sumNat_add]
      unfold cardPrefix
      apply sumNat_congr
      intro x _
      cases x with
      | zero => simp [isRunStart]
      | succ k =>
        simp only [isRunStart, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        cases A k <;> cases A (k + 1) <;> simp
    have h2 :
        sumNat (List.range N) (fun x => if isRunEnd A x then 1 else 0) +
        sumNat (List.range N) (fun x => if A x && A (x + 1) then 1 else 0) =
        cardPrefix A N := by
      rw [← sumNat_add]
      unfold cardPrefix
      apply sumNat_congr
      intro x _
      unfold isRunEnd
      cases A x <;> cases A (x + 1) <;> simp
    have hshift :
        sumNat (List.range N) (fun x => if (if x = 0 then false else A (x - 1) && A x) then 1 else 0) =
        sumNat (List.range N) (fun x => if A x && A (x + 1) then 1 else 0) := by
      cases N with
      | zero => simp [sumNat]
      | succ m =>
        have hlhs :
            sumNat (List.range (m + 1)) (fun x => if (if x = 0 then false else A (x - 1) && A x) then 1 else 0) =
            sumNat (List.range m) (fun x => if A x && A (x + 1) then 1 else 0) := by
          rw [List.range_succ_eq_map, sumNat, sumNat_map]
          simp only [↓reduceIte, Bool.false_eq_true, Nat.zero_add]
          apply sumNat_congr
          intro x _
          simp [Nat.succ_eq_add_one]
        have hrhs :
            sumNat (List.range (m + 1)) (fun x => if A x && A (x + 1) then 1 else 0) =
            sumNat (List.range m) (fun x => if A x && A (x + 1) then 1 else 0) := by
          rw [List.range_succ, sumNat_append]
          have hAm : A (m + 1) = false := hbound (m + 1) (by omega)
          simp [sumNat, hAm]
        rw [hlhs, hrhs]
    omega
  -- Pointwise identity using no-three-consecutive property
  have hpoint : ∀ x : Nat,
      (if isRunStart A x then 1 else 0) + (if isRunEnd A x then 1 else 0) =
      (if A x then 1 else 0) + (if isIsolated A x then 1 else 0) := by
    intro x
    cases x with
    | zero =>
      unfold isIsolated isRunStart isRunEnd
      simp only [↓reduceIte]
      cases A 0 <;> cases A 1 <;> simp
    | succ k =>
      have hno3 := sidon_no_three_consec A hsid k
      unfold isIsolated isRunStart isRunEnd
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      cases hk0 : A k <;> cases hk1 : A (k + 1) <;> cases hk2 : A (k + 2) <;> simp
      exact False.elim (hno3 ⟨hk0, hk1, hk2⟩)
  have hsum := sumNat_congr (List.range N)
    (fun x => (if isRunStart A x then 1 else 0) + (if isRunEnd A x then 1 else 0))
    (fun x => (if A x then 1 else 0) + (if isIsolated A x then 1 else 0))
    (fun x _ => hpoint x)
  rw [sumNat_add, sumNat_add] at hsum
  unfold runsPrefix cardPrefix isolatedPrefix at *
  omega

-- ============================================================================
-- Theorem 3: Descents + LIS <= Length (All Lists; Tight for Avoids231)
-- ============================================================================

theorem des_add_incSubseq_le_length (xs sub : List Nat)
    (hsub : sub.Sublist xs) (hinc : sub.Pairwise (· < ·)) :
    desList xs + sub.length ≤ xs.length := by
  match xs, sub with
  | [], [] => simp [desList]
  | [], _ :: _ => cases hsub
  | [x], [] => simp [desList]
  | [x], _ :: _ =>
    cases hsub with
    | cons _ h => cases h
    | cons_cons _ h => cases h; simp [desList]
  | x :: y :: rest, [] =>
    have hsub0 : ([] : List Nat).Sublist (y :: rest) := List.nil_sublist _
    have ih := des_add_incSubseq_le_length (y :: rest) [] hsub0 List.Pairwise.nil
    simp only [desList, List.length_nil, List.length_cons, Nat.add_zero] at *
    by_cases hxy : x > y <;> simp [hxy] <;> omega
  | x :: y :: rest, z :: sub' =>
    cases hsub with
    | cons _ hsub' =>
      have ih := des_add_incSubseq_le_length (y :: rest) (z :: sub') hsub' hinc
      simp only [desList, List.length_cons] at *
      by_cases hxy : x > y <;> simp [hxy] <;> omega
    | cons_cons _ hsub' =>
      have hinc' : sub'.Pairwise (· < ·) := (List.pairwise_cons.mp hinc).2
      have hgt : ∀ w ∈ sub', x < w := (List.pairwise_cons.mp hinc).1
      simp only [desList, List.length_cons]
      by_cases hxy : x > y
      · simp only [hxy, ↓reduceIte]
        -- Since every w ∈ sub' has x < w and x > y, y cannot match sub'.head; hence sub' ⊆ rest
        have hsub_rest : sub'.Sublist rest := by
          cases hsub' with
          | cons _ hr => exact hr
          | cons_cons _ hr =>
            have hxy_lt : x < y := hgt y (by simp)
            omega
        have hy_sub : (y :: sub').Sublist (y :: rest) := List.Sublist.cons_cons y hsub_rest
        have hy_inc : (y :: sub').Pairwise (· < ·) :=
          List.pairwise_cons.mpr ⟨fun w hw => Nat.lt_trans hxy (hgt w hw), hinc'⟩
        have ih := des_add_incSubseq_le_length (y :: rest) (y :: sub') hy_sub hy_inc
        simp only [List.length_cons] at ih
        omega
      · simp only [hxy, ↓reduceIte]
        have ih := des_add_incSubseq_le_length (y :: rest) sub' hsub' hinc'
        simp only [List.length_cons] at ih
        omega

theorem perm_des_add_incSubseq_le {n : Nat} (p : PermFin n) (sub : List Nat)
    (hinc : PermFin.StrictIncSubseq sub p.toList) :
    desList p.toList + sub.length ≤ n := by
  have hlen : p.toList.length = n := by
    simp [PermFin.toList]
  have h := des_add_incSubseq_le_length p.toList sub hinc.1 hinc.2
  omega

-- ============================================================================
-- Theorem 4: 321-Avoiding Permutations (wexc <-> lrmax and |p(i)-i| <= lis)
-- ============================================================================

namespace PermFin

theorem avoids321_wexc_iff_lrmax {n : Nat} (p : PermFin n) (h321 : p.Avoids321) (i : Fin n) :
    p.IsWeakExcedance i ↔ p.IsLeftToRightMax i := by
  constructor
  · intro hwexc j hj
    apply Classical.byContradiction
    intro hle
    have hge : (p.toFun i).val ≤ (p.toFun j).val := Nat.le_of_not_lt hle
    have hne : p.toFun j ≠ p.toFun i := by
      intro heq
      have hji := p.toFun_inj heq
      omega
    have hgt : (p.toFun i).val < (p.toFun j).val :=
      Nat.lt_of_le_of_ne hge (fun h => hne (Fin.ext h.symm))
    -- By pigeonhole, count of indices < i minus {j} is i.val - 1, which is < (p i).val
    -- so at least one value y < (p i).val has preimage k >= i (and k != i), forming 321!
    have hex_k : ∃ k : Fin n, i.val < k.val ∧ (p.toFun k).val < (p.toFun i).val := by
      apply Classical.byContradiction
      intro hnone
      have hmap : ∀ y ∈ List.finRange n,
          decide (y.val < (p.toFun i).val) = true →
          p.invFun y ∈ List.finRange n ∧
          (decide ((p.invFun y).val < i.val) && decide (p.invFun y ≠ j)) = true := by
        intro y _ hy
        simp only [decide_eq_true_eq] at hy
        refine ⟨List.mem_finRange _, ?_⟩
        have hnotgt : ¬ (i.val < (p.invFun y).val) := by
          intro hlt
          apply hnone
          refine ⟨p.invFun y, hlt, ?_⟩
          rw [p.right_inv]
          exact hy
        have hnei : p.invFun y ≠ i := by
          intro heq
          have : y = p.toFun i := by rw [← heq, p.right_inv]
          omega
        have hlt_i : (p.invFun y).val < i.val := by
          have : (p.invFun y).val ≠ i.val := fun h => hnei (Fin.ext h)
          omega
        have hnej : p.invFun y ≠ j := by
          intro heq
          have : y = p.toFun j := by rw [← heq, p.right_inv]
          omega
        simp [hlt_i, hnej]
      have hcnt := countP_map_le p.invFun (fun _ _ h => p.invFun_inj h)
        (List.finRange n) (List.finRange n) (List.nodup_finRange n) (List.nodup_finRange n)
        (fun y => decide (y.val < (p.toFun i).val))
        (fun x => decide (x.val < i.val) && decide (x ≠ j)) hmap
      rw [countP_finRange_lt] at hcnt
      rw [Nat.min_eq_left (Nat.le_of_lt (p.toFun i).isLt)] at hcnt
      have hrhs_le : (List.finRange n).countP (fun x => decide (x.val < i.val) && decide (x ≠ j)) + 1 ≤
          (List.finRange n).countP (fun x => decide (x.val < i.val)) := by
        rw [countP_eq_sumNat, countP_eq_sumNat]
        have hind := sumNat_eq_indicator_one (List.finRange n) (List.nodup_finRange n) j (List.mem_finRange j)
        rw [show (sumNat (List.finRange n) fun x => if (decide (x.val < i.val) && decide (x ≠ j)) = true then 1 else 0) + 1 =
            (sumNat (List.finRange n) fun x => if (decide (x.val < i.val) && decide (x ≠ j)) = true then 1 else 0) +
            sumNat (List.finRange n) (fun x => if x = j then 1 else 0) by rw [hind]]
        rw [← sumNat_add]
        apply sumNat_mono
        intro x _
        by_cases hxj : x = j
        · subst hxj; simp [hj]
        · by_cases hxi : x.val < i.val <;> simp [hxj, hxi]
      rw [countP_finRange_lt, Nat.min_eq_left (Nat.le_of_lt i.isLt)] at hrhs_le
      unfold IsWeakExcedance at hwexc
      omega
    rcases hex_k with ⟨k, hik, hpk⟩
    exact h321 j i k hj hik ⟨hgt, hpk⟩
  · intro hlrmax
    apply Classical.byContradiction
    intro hlt
    have hp_lt : (p.toFun i).val < i.val := Nat.lt_of_not_le hlt
    have hmap : ∀ x ∈ List.finRange n,
        decide (x.val < i.val) = true →
        p.toFun x ∈ List.finRange n ∧ decide ((p.toFun x).val < (p.toFun i).val) = true := by
      intro x _ hx
      simp only [decide_eq_true_eq] at hx ⊢
      exact ⟨List.mem_finRange _, hlrmax x hx⟩
    have hcnt := countP_map_le p.toFun (fun _ _ h => p.toFun_inj h)
      (List.finRange n) (List.finRange n) (List.nodup_finRange n) (List.nodup_finRange n)
      (fun x => decide (x.val < i.val)) (fun y => decide (y.val < (p.toFun i).val)) hmap
    rw [countP_finRange_lt, countP_finRange_lt,
        Nat.min_eq_left (Nat.le_of_lt i.isLt),
        Nat.min_eq_left (Nat.le_of_lt (p.toFun i).isLt)] at hcnt
    omega

private theorem finRange_pairwise_lt (n : Nat) :
    (List.finRange n).Pairwise (fun a b : Fin n => a.val < b.val) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ_last, List.pairwise_append]
    refine ⟨?_, by simp, ?_⟩
    · rw [List.pairwise_map]
      exact List.Pairwise.imp (fun h => h) ih
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      rw [List.mem_map] at ha
      rcases ha with ⟨x, _, rfl⟩
      exact x.isLt

private theorem filter_finRange_inc_subseq {n : Nat} (p : PermFin n)
    (Q : Fin n → Bool)
    (hinc : ∀ a b : Fin n, Q a = true → Q b = true → a.val < b.val → (p.toFun a).val < (p.toFun b).val) :
    StrictIncSubseq (((List.finRange n).filter Q).map (fun k => (p.toFun k).val)) p.toList := by
  constructor
  · exact List.Sublist.map _ List.filter_sublist
  · rw [List.pairwise_map]
    have hpw := List.Pairwise.filter Q (finRange_pairwise_lt n)
    refine List.Pairwise.imp_of_mem ?_ hpw
    intro a b ha hb hab
    rw [List.mem_filter] at ha hb
    exact hinc a b ha.2 hb.2 hab

private theorem length_filter_eq_countP {α : Type} (P : α → Bool) (xs : List α) :
    (xs.filter P).length = xs.countP P := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.filter_cons, List.countP_cons]
    cases P x <;> simp [ih]

theorem avoids321_disp_bound {n : Nat} (p : PermFin n) (h321 : p.Avoids321) (i : Fin n) :
    ∃ sub : List Nat, StrictIncSubseq sub p.toList ∧
      natAbsDiff (p.toFun i).val i.val ≤ sub.length := by
  by_cases hle : i.val ≤ (p.toFun i).val
  · -- Case 1: p(i) >= i; take {k > i | p(k) < p(i)}
    let Q : Fin n → Bool := fun k => decide (i.val < k.val) && decide ((p.toFun k).val < (p.toFun i).val)
    have hinc : ∀ a b, Q a = true → Q b = true → a.val < b.val → (p.toFun a).val < (p.toFun b).val := by
      intro a b ha hb hab
      simp only [Q, Bool.and_eq_true, decide_eq_true_eq] at ha hb
      apply Classical.byContradiction
      intro hle_ab
      have hge : (p.toFun b).val ≤ (p.toFun a).val := Nat.le_of_not_lt hle_ab
      have hne : p.toFun a ≠ p.toFun b := fun h => by have := p.toFun_inj h; omega
      have hgt : (p.toFun a).val > (p.toFun b).val := Nat.lt_of_le_of_ne hge (fun h => hne (Fin.ext h.symm))
      exact h321 i a b ha.1 hab ⟨ha.2, hgt⟩
    refine ⟨((List.finRange n).filter Q).map (fun k => (p.toFun k).val),
            filter_finRange_inc_subseq p Q hinc, ?_⟩
    rw [List.length_map, length_filter_eq_countP]
    -- Show count of {y < p(i)} <= count of {x < i} + countP Q
    have hmap : ∀ y ∈ List.finRange n,
        decide (y.val < (p.toFun i).val) = true →
        p.invFun y ∈ List.finRange n ∧
        (decide ((p.invFun y).val < i.val) || Q (p.invFun y)) = true := by
      intro y _ hy
      simp only [decide_eq_true_eq] at hy
      refine ⟨List.mem_finRange _, ?_⟩
      have hnei : p.invFun y ≠ i := fun heq => by
        have : y = p.toFun i := by rw [← heq, p.right_inv]
        omega
      rcases Nat.lt_trichotomy (p.invFun y).val i.val with hlt | heq | hgt
      · simp [hlt]
      · exact False.elim (hnei (Fin.ext heq))
      · simp [Q, hgt, p.right_inv, hy]
    have hcnt := countP_map_le p.invFun (fun _ _ h => p.invFun_inj h)
      (List.finRange n) (List.finRange n) (List.nodup_finRange n) (List.nodup_finRange n)
      (fun y => decide (y.val < (p.toFun i).val))
      (fun x => decide (x.val < i.val) || Q x) hmap
    rw [countP_finRange_lt] at hcnt
    have hsplit : (List.finRange n).countP (fun x => decide (x.val < i.val) || Q x) ≤
        (List.finRange n).countP (fun x => decide (x.val < i.val)) + (List.finRange n).countP Q := by
      rw [countP_eq_sumNat, countP_eq_sumNat, countP_eq_sumNat, ← sumNat_add]
      apply sumNat_mono
      intro x _
      cases decide (x.val < i.val) <;> cases Q x <;> simp
    rw [countP_finRange_lt, Nat.min_eq_left (Nat.le_of_lt i.isLt)] at hsplit
    rw [Nat.min_eq_left (Nat.le_of_lt (p.toFun i).isLt)] at hcnt
    unfold natAbsDiff
    split <;> omega
  · -- Case 2: p(i) < i; take {j < i | p(j) > p(i)}
    have hp_lt : (p.toFun i).val < i.val := Nat.lt_of_not_le hle
    let Q : Fin n → Bool := fun j => decide (j.val < i.val) && decide ((p.toFun i).val < (p.toFun j).val)
    have hinc : ∀ a b, Q a = true → Q b = true → a.val < b.val → (p.toFun a).val < (p.toFun b).val := by
      intro a b ha hb hab
      simp only [Q, Bool.and_eq_true, decide_eq_true_eq] at ha hb
      apply Classical.byContradiction
      intro hle_ab
      have hge : (p.toFun b).val ≤ (p.toFun a).val := Nat.le_of_not_lt hle_ab
      have hne : p.toFun a ≠ p.toFun b := fun h => by have := p.toFun_inj h; omega
      have hgt : (p.toFun a).val > (p.toFun b).val := Nat.lt_of_le_of_ne hge (fun h => hne (Fin.ext h.symm))
      exact h321 a b i hab hb.1 ⟨hgt, hb.2⟩
    refine ⟨((List.finRange n).filter Q).map (fun k => (p.toFun k).val),
            filter_finRange_inc_subseq p Q hinc, ?_⟩
    rw [List.length_map, length_filter_eq_countP]
    -- Split countP (j < i) = countP (j < i && p j < p i) + countP (j < i && p i < p j)!
    have hpart : (List.finRange n).countP (fun j => decide (j.val < i.val)) =
        (List.finRange n).countP (fun j => decide (j.val < i.val) && decide ((p.toFun j).val < (p.toFun i).val)) +
        (List.finRange n).countP Q := by
      rw [countP_eq_sumNat, countP_eq_sumNat, countP_eq_sumNat, ← sumNat_add]
      apply sumNat_congr
      intro j _
      by_cases hj : j.val < i.val
      · by_cases h1 : (p.toFun j).val < (p.toFun i).val <;>
          by_cases h2 : (p.toFun i).val < (p.toFun j).val <;>
          simp [Q, hj, h1, h2]
        · omega
        · have : p.toFun j = p.toFun i := Fin.ext (by omega)
          have hji : j = i := p.toFun_inj this
          subst hji; omega
      · simp [Q, hj]
    have hmap2 : ∀ j ∈ List.finRange n,
        (decide (j.val < i.val) && decide ((p.toFun j).val < (p.toFun i).val)) = true →
        p.toFun j ∈ List.finRange n ∧ decide ((p.toFun j).val < (p.toFun i).val) = true := by
      intro j _ hj
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
      exact ⟨List.mem_finRange _, decide_eq_true hj.2⟩
    have hcnt2 := countP_map_le p.toFun (fun _ _ h => p.toFun_inj h)
      (List.finRange n) (List.finRange n) (List.nodup_finRange n) (List.nodup_finRange n)
      (fun j => decide (j.val < i.val) && decide ((p.toFun j).val < (p.toFun i).val))
      (fun y => decide (y.val < (p.toFun i).val)) hmap2
    rw [countP_finRange_lt] at hpart hcnt2
    rw [Nat.min_eq_left (Nat.le_of_lt (p.toFun i).isLt)] at hcnt2
    rw [Nat.min_eq_left (Nat.le_of_lt i.isLt)] at hpart
    unfold natAbsDiff
    split <;> omega

-- ============================================================================
-- Theorem 7: 231-Avoiding Inversions vs Displacement + C(des + 1, 2)
-- ============================================================================

private theorem sumNat_zero {α : Type} (xs : List α) : sumNat xs (fun _ => 0) = 0 := by
  induction xs <;> simp [sumNat, *]

private theorem nodup_filter {α : Type} (P : α → Bool) {xs : List α} (h : xs.Nodup) :
    (xs.filter P).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    rw [List.nodup_cons] at h
    simp only [List.filter_cons]
    cases hpx : P x
    · exact ih h.2
    · simp only [↓reduceIte, List.nodup_cons]
      refine ⟨fun hm => h.1 ((List.mem_filter.mp hm).1), ih h.2⟩

private theorem desList_range_map (n : Nat) (g : Nat → Nat) :
    desList ((List.range n).map g) =
    (List.range (n - 1)).countP (fun i => decide (g (i + 1) < g i)) := by
  induction n generalizing g with
  | zero => simp [desList]
  | succ m ih =>
    cases m with
    | zero => simp [desList]
    | succ k =>
      have h1 : (List.range (k + 2)).map g = g 0 :: (List.range (k + 1)).map (fun t => g (t + 1)) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map]
        rfl
      have h2 : (List.range (k + 1)).map (fun t => g (t + 1)) =
          g 1 :: (List.range k).map (fun t => g (t + 2)) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map]
        rfl
      have ih1 := ih (fun t => g (t + 1))
      simp only [Nat.add_sub_cancel] at ih1
      have hr : (List.range (k + 1)).countP (fun i => decide (g (i + 1) < g i)) =
          (if g 1 < g 0 then 1 else 0) + (List.range k).countP (fun t => decide (g (t + 2) < g (t + 1))) := by
        rw [List.range_succ_eq_map, List.countP_cons, List.countP_map]
        have hcomp : ((fun i => decide (g (i + 1) < g i)) ∘ Nat.succ) = (fun t => decide (g (t + 2) < g (t + 1))) := by
          funext t; rfl
        rw [hcomp]
        by_cases h01 : g 1 < g 0 <;> simp [h01] <;> omega
      have ih_rw : desList (g 1 :: (List.range k).map (fun t => g (t + 2))) =
          (List.range k).countP (fun t => decide (g (t + 2) < g (t + 1))) := by
        rw [← h2]; exact ih1
      rw [h1, h2]
      simp only [desList, Nat.add_sub_cancel]
      rw [ih_rw, hr]

theorem avoids231_exc_le_des {m : Nat} (q : PermFin m) (hq : q.Avoids231) :
    q.excCnt ≤ desList q.toList := by
  have hstep : ∀ j : Fin m, j.val < (q.toFun j).val →
      ∃ hjm : j.val + 1 < m, (q.toFun ⟨j.val + 1, hjm⟩).val < (q.toFun j).val := by
    intro j hj
    have hjm : j.val + 1 < m := by
      have hp := (q.toFun j).isLt
      omega
    refine ⟨hjm, ?_⟩
    apply Classical.byContradiction
    intro hle
    have hne : q.toFun j ≠ q.toFun ⟨j.val + 1, hjm⟩ := fun h => by
      have := Fin.ext_iff.mp (q.toFun_inj h)
      dsimp at this
      omega
    have hgt : (q.toFun j).val < (q.toFun ⟨j.val + 1, hjm⟩).val := by
      have : (q.toFun j).val ≠ (q.toFun ⟨j.val + 1, hjm⟩).val := fun h => hne (Fin.ext h)
      omega
    have hmap : ∀ y ∈ List.finRange m,
        decide (y.val < (q.toFun j).val) = true →
        q.invFun y ∈ List.finRange m ∧ decide ((q.invFun y).val < j.val) = true := by
      intro y _ hy
      simp only [decide_eq_true_eq] at hy
      refine ⟨List.mem_finRange _, decide_eq_true ?_⟩
      have hnoj : q.invFun y ≠ j := fun h => by
        have := congrArg q.toFun h
        rw [q.right_inv] at this
        subst this
        omega
      have hnot_gt : ¬ (j.val < (q.invFun y).val) := by
        intro hjr
        by_cases hr1 : (q.invFun y).val = j.val + 1
        · have heq : q.invFun y = ⟨j.val + 1, hjm⟩ := Fin.ext hr1
          have := congrArg q.toFun heq
          rw [q.right_inv] at this
          omega
        · have hj1 : j.val + 1 < (q.invFun y).val := by omega
          apply hq j ⟨j.val + 1, hjm⟩ (q.invFun y) (by simp) hj1
          refine ⟨?_, hgt⟩
          rw [q.right_inv]
          exact hy
      have hne_val : (q.invFun y).val ≠ j.val := fun h => hnoj (Fin.ext h)
      omega
    have hcnt := countP_map_le q.invFun (fun _ _ h => q.invFun_inj h)
      (List.finRange m) (List.finRange m) (List.nodup_finRange m) (List.nodup_finRange m)
      (fun y => decide (y.val < (q.toFun j).val))
      (fun x => decide (x.val < j.val)) hmap
    rw [countP_finRange_lt, countP_finRange_lt,
        Nat.min_eq_left (Nat.le_of_lt (q.toFun j).isLt),
        Nat.min_eq_left (Nat.le_of_lt j.isLt)] at hcnt
    omega
  let g : Nat → Nat := fun i => if h : i < m then (q.toFun ⟨i, h⟩).val else 0
  have htoList : q.toList = (List.range m).map g := by
    unfold PermFin.toList
    rw [← finRange_map_val m, List.map_map]
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_def, g, x.isLt, ↓reduceDIte]
  rw [htoList, desList_range_map]
  have hexc_range : q.excCnt = (List.range m).countP (fun i => decide (i < g i)) := by
    unfold PermFin.excCnt
    have h1 : (List.finRange m).countP (fun i => decide (i.val < (q.toFun i).val)) =
        (List.finRange m).countP (fun i => decide (i.val < g i.val)) := by
      rw [countP_eq_sumNat, countP_eq_sumNat]
      apply sumNat_congr
      intro i _
      simp [g, i.isLt]
    rw [h1, ← finRange_map_val m, List.countP_map]
    rfl
  rw [hexc_range]
  cases m with
  | zero => simp
  | succ m' =>
    rw [Nat.add_sub_cancel]
    have hlast : ¬ (m' < g m') := by
      simp only [g, Nat.lt_succ_self, ↓reduceDIte]
      have := (q.toFun ⟨m', Nat.lt_succ_self m'⟩).isLt
      omega
    have hdrop : (List.range (m' + 1)).countP (fun i => decide (i < g i)) =
        (List.range m').countP (fun i => decide (i < g i)) := by
      rw [List.range_succ, List.countP_append]
      simp [hlast]
    rw [hdrop, countP_eq_sumNat, countP_eq_sumNat]
    apply sumNat_mono
    intro i hi
    rw [List.mem_range] at hi
    by_cases hgi : i < g i
    · have him : i < m' + 1 := by omega
      have hgi' : i < (q.toFun ⟨i, him⟩).val := by simpa [g, him] using hgi
      rcases hstep ⟨i, him⟩ hgi' with ⟨hjm, hdec⟩
      have hdecg : g (i + 1) < g i := by simpa [g, him, hjm] using hdec
      simp [hgi, hdecg]
    · simp [hgi]

private theorem map_finRange_eq_range_countP (n : Nat) (P : Nat → Bool) :
    (List.finRange n).countP (fun i => P i.val) = (List.range n).countP P := by
  rw [← finRange_map_val n, List.countP_map]
  rfl

private theorem sumNat_finRange_eq_range (n : Nat) (f : Nat → Nat) :
    sumNat (List.finRange n) (fun i => f i.val) = sumNat (List.range n) f := by
  rw [← finRange_map_val n, sumNat_map]

private theorem desList_append_split (xs ys : List Nat) (a b : Nat)
    (hxa : ∀ x ∈ xs, x < a) (hay : a > b) :
    desList (xs ++ a :: b :: ys) = desList xs + 1 + desList (b :: ys) := by
  induction xs with
  | nil =>
    simp only [List.nil_append, desList, hay, ↓reduceIte]
  | cons x rest ih =>
    cases rest with
    | nil =>
      have hx : x < a := hxa x (by simp)
      have hnot : ¬ (x > a) := by omega
      simp only [List.cons_append, List.nil_append, desList, hnot, ↓reduceIte, hay]
      omega
    | cons y rrest =>
      have ih' := ih (fun w hw => hxa w (by simp [hw]))
      simp only [List.cons_append, desList] at ih' ⊢
      by_cases hxy : x > y <;> simp [hxy] <;> omega

private theorem desList_map_add (xs : List Nat) (c : Nat) :
    desList (xs.map (· + c)) = desList xs := by
  match xs with
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest =>
    have ih := desList_map_add (y :: rest) c
    simp only [List.map_cons, desList] at ih ⊢
    by_cases hxy : x > y
    · have hc : x + c > y + c := by omega
      simp [hxy, hc, ih]
    · have hnc : ¬ (x + c > y + c) := by omega
      simp [hxy, hnc, ih]

private theorem desList_append_last_lt (xs : List Nat) (a : Nat) (hxa : ∀ x ∈ xs, x < a) :
    desList (xs ++ [a]) = desList xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases rest with
    | nil =>
      have hx : x < a := hxa x (by simp)
      have hnot : ¬ (x > a) := by omega
      simp [desList, hnot]
    | cons y rrest =>
      have ih' := ih (fun w hw => hxa w (by simp [hw]))
      simp only [List.cons_append, desList] at ih' ⊢
      by_cases hxy : x > y <;> simp [hxy, ih']

private theorem sumNat_finRange_congr_range (m : Nat) (f : Fin m → Nat) (g : Nat → Nat)
    (h : ∀ i : Fin m, f i = g i.val) : sumNat (List.finRange m) f = sumNat (List.range m) g := by
  rw [← sumNat_finRange_eq_range m g]
  exact sumNat_congr (List.finRange m) f (fun i => g i.val) (fun i _ => h i)

private theorem des_quad_le (a b : Nat) :
    a * (a + 1) + b * (b + 1) + 2 * b ≤ (a + 1 + b) * (a + 1 + b + 1) := by
  have hcm : b * a = a * b := Nat.mul_comm b a
  have h1 : (a + 1 + b) * (a + 1 + b + 1) =
      a * (a + 1) + b * (b + 1) + 2 * b + 2 * a * b + 2 * a + 2 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.mul_assoc, hcm]
    omega
  omega

private theorem range_split_at (m k : Nat) (hk : k ≤ m) :
    List.range (m + 1) = List.range k ++ k :: (List.range (m - k)).map (k + 1 + ·) := by
  have hr : m + 1 = k + ((m - k) + 1) := by omega
  rw [hr, List.range_add, List.range_succ_eq_map, List.map_cons, Nat.add_zero, List.map_map]
  congr 1
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_def]
  omega

private theorem sumNat_range_split_at (m k : Nat) (hk : k ≤ m) (f : Nat → Nat) :
    sumNat (List.range (m + 1)) f =
    sumNat (List.range k) f + f k + sumNat (List.range (m - k)) (fun r => f (k + 1 + r)) := by
  have h1 := range_split_at m k hk
  rw [h1, sumNat_append, sumNat, sumNat_map]
  omega

private theorem countP_range_split_at (m k : Nat) (hk : k ≤ m) (P : Nat → Bool) :
    (List.range (m + 1)).countP P =
    (List.range k).countP P + (if P k then 1 else 0) + (List.range (m - k)).countP (fun r => P (k + 1 + r)) := by
  rw [countP_eq_sumNat, countP_eq_sumNat, countP_eq_sumNat]
  exact sumNat_range_split_at m k hk (fun x => if P x then 1 else 0)

private theorem sumNat_finRange_split_at (m k : Nat) (hk : k ≤ m) (f : Fin (m + 1) → Nat) :
    sumNat (List.finRange (m + 1)) f =
    sumNat (List.range k) (fun i => if hi : i < m + 1 then f ⟨i, hi⟩ else 0) +
    f ⟨k, by omega⟩ +
    sumNat (List.range (m - k)) (fun r => if hr : k + 1 + r < m + 1 then f ⟨k + 1 + r, hr⟩ else 0) := by
  have hfin : sumNat (List.finRange (m + 1)) f =
      sumNat (List.range (m + 1)) (fun i => if hi : i < m + 1 then f ⟨i, hi⟩ else 0) := by
    rw [← finRange_map_val (m + 1), sumNat_map]
    apply sumNat_congr
    intro x _
    simp [x.isLt]
  rw [hfin, sumNat_range_split_at m k hk]
  simp [(by omega : k < m + 1)]

private theorem permFin_zero_invCnt {r : Nat} (hr : r = 0) (q : PermFin r) : q.invCnt = 0 := by
  subst hr; simp [PermFin.invCnt, sumNat]

private theorem permFin_zero_disp2 {r : Nat} (hr : r = 0) (q : PermFin r) : q.disp2 = 0 := by
  subst hr; simp [PermFin.disp2, sumNat]

private theorem permFin_zero_excCnt {r : Nat} (hr : r = 0) (q : PermFin r) : q.excCnt = 0 := by
  subst hr; simp [PermFin.excCnt]

private theorem permFin_zero_toList {r : Nat} (hr : r = 0) (q : PermFin r) : q.toList = [] := by
  subst hr; simp [PermFin.toList]

private theorem permFin_succ_toList_ne {r r' : Nat} (hr : r = r' + 1) (q : PermFin r) :
    q.toList ≠ [] := by
  subst hr; unfold PermFin.toList; rw [List.finRange_succ]; simp

private theorem avoids231_two_inv_aux :
    ∀ bound n : Nat, n ≤ bound → ∀ p : PermFin n, p.Avoids231 →
      2 * p.invCnt ≤ p.disp2 + desList p.toList * (desList p.toList + 1) := by
  intro bound
  induction bound with
  | zero =>
    intro n hn p _
    have hn0 : n = 0 := by omega
    subst hn0
    simp [PermFin.invCnt, PermFin.disp2, PermFin.toList, desList, sumNat]
  | succ m ih =>
    intro n hn p h231
    cases n with
    | zero => simp [PermFin.invCnt, PermFin.disp2, PermFin.toList, desList, sumNat]
    | succ n' =>
      have hn' : n' ≤ m := by omega
      let top : Fin (n' + 1) := ⟨n', Nat.lt_succ_self n'⟩
      let k : Fin (n' + 1) := p.invFun top
      have hk_le : k.val ≤ n' := Nat.le_of_lt_succ k.isLt
      have hpk : p.toFun k = top := p.right_inv top
      have hpk_val : (p.toFun k).val = n' := by simpa [top] using congrArg Fin.val hpk
      have hleft_lt : ∀ i : Fin (n' + 1), i.val < k.val → (p.toFun i).val < k.val := by
        intro i hik
        apply Classical.byContradiction
        intro hge
        have hlt_top : (p.toFun i).val < n' := by
          have hne : p.toFun i ≠ top := by
            intro heq
            have : i = k := p.toFun_inj (heq.trans hpk.symm)
            omega
          have hi_lt := (p.toFun i).isLt
          have hnev : (p.toFun i).val ≠ n' := fun hv => hne (Fin.ext hv)
          omega
        have hmap : ∀ y ∈ List.finRange (n' + 1),
            decide (y.val < (p.toFun i).val) = true →
            p.invFun y ∈ List.finRange (n' + 1) ∧
            (decide ((p.invFun y).val < k.val) && decide (p.invFun y ≠ i)) = true := by
          intro y _ hy
          simp only [decide_eq_true_eq] at hy
          refine ⟨List.mem_finRange _, ?_⟩
          have hnei : p.invFun y ≠ i := fun heq => by
            have := congrArg p.toFun heq
            rw [p.right_inv] at this
            subst this
            omega
          have hnek : p.invFun y ≠ k := fun heq => by
            have := congrArg p.toFun heq
            rw [p.right_inv, hpk] at this
            have hy_eq : y.val = n' := by simpa [top] using congrArg Fin.val this
            omega
          have hnot_gt : ¬ (k.val < (p.invFun y).val) := by
            intro hkj
            apply h231 i k (p.invFun y) hik hkj
            refine ⟨?_, by rw [hpk_val]; exact hlt_top⟩
            rw [p.right_inv]
            exact hy
          have hnekv : (p.invFun y).val ≠ k.val := fun hv => hnek (Fin.ext hv)
          have hlt_k : (p.invFun y).val < k.val := by omega
          simp [hlt_k, hnei]
        have hcnt := countP_map_le p.invFun (fun _ _ h => p.invFun_inj h)
          (List.finRange (n' + 1)) (List.finRange (n' + 1))
          (List.nodup_finRange (n' + 1)) (List.nodup_finRange (n' + 1))
          (fun y => decide (y.val < (p.toFun i).val))
          (fun x => decide (x.val < k.val) && decide (x ≠ i)) hmap
        rw [countP_finRange_lt, Nat.min_eq_left (Nat.le_of_lt (p.toFun i).isLt)] at hcnt
        have hle_k : (List.finRange (n' + 1)).countP (fun x => decide (x.val < k.val) && decide (x ≠ i)) + 1 ≤
            (List.finRange (n' + 1)).countP (fun x => decide (x.val < k.val)) := by
          rw [countP_eq_sumNat, countP_eq_sumNat]
          have hind := sumNat_eq_indicator_one (List.finRange (n' + 1)) (List.nodup_finRange (n' + 1)) i (List.mem_finRange i)
          rw [show (sumNat (List.finRange (n' + 1)) fun x => if (decide (x.val < k.val) && decide (x ≠ i)) = true then 1 else 0) + 1 =
              (sumNat (List.finRange (n' + 1)) fun x => if (decide (x.val < k.val) && decide (x ≠ i)) = true then 1 else 0) +
              sumNat (List.finRange (n' + 1)) (fun x => if x = i then 1 else 0) by rw [hind]]
          rw [← sumNat_add]
          apply sumNat_mono
          intro x _
          by_cases hxi : x = i
          · subst hxi; simp [hik]
          · by_cases hxk : x.val < k.val <;> simp [hxi, hxk]
        rw [countP_finRange_lt, Nat.min_eq_left (Nat.le_of_lt k.isLt)] at hle_k
        omega
      have hright_ge : ∀ j : Fin (n' + 1), k.val < j.val → k.val ≤ (p.toFun j).val := by
        intro j hkj
        apply Classical.byContradiction
        intro hlt
        have hj_lt : (p.toFun j).val < k.val := Nat.lt_of_not_le hlt
        have hmap : ∀ x ∈ List.finRange (n' + 1),
            (decide (x.val < k.val) || decide (x = j)) = true →
            p.toFun x ∈ List.finRange (n' + 1) ∧ decide ((p.toFun x).val < k.val) = true := by
          intro x _ hx
          refine ⟨List.mem_finRange _, decide_eq_true ?_⟩
          rcases Bool.or_eq_true _ _ |>.mp hx with hx1 | hx2
          · exact hleft_lt x (decide_eq_true_eq.mp hx1)
          · have hxj : x = j := decide_eq_true_eq.mp hx2
            subst hxj; exact hj_lt
        have hcnt := countP_map_le p.toFun (fun _ _ h => p.toFun_inj h)
          (List.finRange (n' + 1)) (List.finRange (n' + 1))
          (List.nodup_finRange (n' + 1)) (List.nodup_finRange (n' + 1))
          (fun x => decide (x.val < k.val) || decide (x = j))
          (fun y => decide (y.val < k.val)) hmap
        rw [countP_finRange_lt, Nat.min_eq_left (Nat.le_of_lt k.isLt)] at hcnt
        have hge_k : (List.finRange (n' + 1)).countP (fun x => decide (x.val < k.val)) + 1 ≤
            (List.finRange (n' + 1)).countP (fun x => decide (x.val < k.val) || decide (x = j)) := by
          rw [countP_eq_sumNat, countP_eq_sumNat]
          have hind := sumNat_eq_indicator_one (List.finRange (n' + 1)) (List.nodup_finRange (n' + 1)) j (List.mem_finRange j)
          rw [show (sumNat (List.finRange (n' + 1)) fun x => if decide (x.val < k.val) = true then 1 else 0) + 1 =
              (sumNat (List.finRange (n' + 1)) fun x => if decide (x.val < k.val) = true then 1 else 0) +
              sumNat (List.finRange (n' + 1)) (fun x => if x = j then 1 else 0) by rw [hind]]
          rw [← sumNat_add]
          apply sumNat_mono
          intro x _
          by_cases hxj : x = j
          · subst hxj; have hn : ¬ (x.val < k.val) := by omega
            simp [hn]
          · by_cases hxk : x.val < k.val <;> simp [hxj, hxk]
        rw [countP_finRange_lt, Nat.min_eq_left (Nat.le_of_lt k.isLt)] at hge_k
        omega
      have hright_lt : ∀ j : Fin (n' + 1), k.val < j.val → (p.toFun j).val < n' := by
        intro j hkj
        have hne : p.toFun j ≠ top := fun h => by
          have : j = k := p.toFun_inj (h.trans hpk.symm)
          omega
        have hjlt := (p.toFun j).isLt
        have hnev : (p.toFun j).val ≠ n' := fun hv => hne (Fin.ext hv)
        omega
      have hinv_left : ∀ y : Fin (n' + 1), y.val < k.val → (p.invFun y).val < k.val := by
        intro y hy
        apply Classical.byContradiction
        intro hge
        have hle : k.val ≤ (p.invFun y).val := Nat.le_of_not_lt hge
        by_cases heqk : (p.invFun y).val = k.val
        · have heq : p.invFun y = k := Fin.ext heqk
          have := congrArg p.toFun heq
          rw [p.right_inv, hpk] at this
          have hy_eq : y.val = n' := by simpa [top] using congrArg Fin.val this
          omega
        · have hgt : k.val < (p.invFun y).val := by omega
          have h2 := hright_ge (p.invFun y) hgt
          rw [p.right_inv] at h2
          omega
      have hinv_right : ∀ y : Fin (n' + 1), k.val ≤ y.val → y.val < n' →
          k.val < (p.invFun y).val := by
        intro y hy1 hy2
        apply Classical.byContradiction
        intro hle
        by_cases heqk : (p.invFun y).val = k.val
        · have heq : p.invFun y = k := Fin.ext heqk
          have := congrArg p.toFun heq
          rw [p.right_inv, hpk] at this
          have hy_eq : y.val = n' := by simpa [top] using congrArg Fin.val this
          omega
        · have hlt : (p.invFun y).val < k.val := by omega
          have h1 := hleft_lt (p.invFun y) hlt
          rw [p.right_inv] at h1
          omega
      let pL : PermFin k.val := {
        toFun := fun i => ⟨(p.toFun ⟨i.val, by omega⟩).val, hleft_lt ⟨i.val, by omega⟩ i.isLt⟩
        invFun := fun y => ⟨(p.invFun ⟨y.val, by omega⟩).val, hinv_left ⟨y.val, by omega⟩ y.isLt⟩
        left_inv := fun i => Fin.ext (by
          have h := congrArg Fin.val (p.left_inv ⟨i.val, by omega⟩)
          simpa using h)
        right_inv := fun y => Fin.ext (by
          have h := congrArg Fin.val (p.right_inv ⟨y.val, by omega⟩)
          simpa using h)
      }
      let pR : PermFin (n' - k.val) := {
        toFun := fun j => ⟨(p.toFun ⟨k.val + 1 + j.val, by omega⟩).val - k.val, by
          have hj_lt := j.isLt
          have hlt := hright_lt ⟨k.val + 1 + j.val, by omega⟩ (by dsimp; omega)
          omega⟩
        invFun := fun y => ⟨(p.invFun ⟨k.val + y.val, by omega⟩).val - (k.val + 1), by
          have hy_lt := y.isLt
          have h1 := hinv_right ⟨k.val + y.val, by omega⟩ (by dsimp; omega) (by dsimp; omega)
          have h2 := (p.invFun ⟨k.val + y.val, by omega⟩).isLt
          omega⟩
        left_inv := fun j => Fin.ext (by
          have hj_lt := j.isLt
          have hj_ge := hright_ge ⟨k.val + 1 + j.val, by omega⟩ (by dsimp; omega)
          have heq1 : (⟨k.val + ((p.toFun ⟨k.val + 1 + j.val, by omega⟩).val - k.val), by omega⟩ : Fin (n' + 1)) =
              p.toFun ⟨k.val + 1 + j.val, by omega⟩ := Fin.ext (by dsimp; omega)
          have h := congrArg Fin.val (p.left_inv ⟨k.val + 1 + j.val, by omega⟩)
          dsimp
          rw [heq1]
          dsimp at h
          omega)
        right_inv := fun y => Fin.ext (by
          have hy_lt := y.isLt
          have hr := hinv_right ⟨k.val + y.val, by omega⟩ (by dsimp; omega) (by dsimp; omega)
          have heq1 : (⟨k.val + 1 + ((p.invFun ⟨k.val + y.val, by omega⟩).val - (k.val + 1)), by omega⟩ : Fin (n' + 1)) =
              p.invFun ⟨k.val + y.val, by omega⟩ := Fin.ext (by dsimp; omega)
          have h := congrArg Fin.val (p.right_inv ⟨k.val + y.val, by omega⟩)
          dsimp
          rw [heq1]
          dsimp at h
          omega)
      }
      have hL231 : pL.Avoids231 := by
        intro a b c hab hbc ⟨hca, hcb⟩
        exact h231 ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ ⟨c.val, by omega⟩ hab hbc ⟨hca, hcb⟩
      have hR231 : pR.Avoids231 := by
        intro a b c hab hbc ⟨hca, hcb⟩
        have ha_lt := a.isLt
        have hb_lt := b.isLt
        have hc_lt := c.isLt
        have ha_ge := hright_ge ⟨k.val + 1 + a.val, by omega⟩ (by dsimp; omega)
        have hb_ge := hright_ge ⟨k.val + 1 + b.val, by omega⟩ (by dsimp; omega)
        have hc_ge := hright_ge ⟨k.val + 1 + c.val, by omega⟩ (by dsimp; omega)
        dsimp [pR] at hca hcb
        exact h231 ⟨k.val + 1 + a.val, by omega⟩ ⟨k.val + 1 + b.val, by omega⟩ ⟨k.val + 1 + c.val, by omega⟩
          (by dsimp; omega) (by dsimp; omega) (by refine ⟨by omega, by omega⟩)
      -- 1. Decompose p.invCnt
      have hinv_eq : p.invCnt = pL.invCnt + pR.invCnt + (n' - k.val) := by
        have hinv_lhs : p.invCnt = sumNat (List.finRange (n' + 1)) (fun i =>
            (List.finRange (n' + 1)).countP (fun j => decide (i.val < j.val) && decide ((p.toFun j).val < (p.toFun i).val))) := rfl
        have houter : ∀ i : Fin (n' + 1),
            (List.finRange (n' + 1)).countP (fun j => decide (i.val < j.val) && decide ((p.toFun j).val < (p.toFun i).val)) =
            (List.range k.val).countP (fun j => if hj : j < n' + 1 then decide (i.val < j) && decide ((p.toFun ⟨j, hj⟩).val < (p.toFun i).val) else false) +
            (if i.val < k.val ∧ (p.toFun k).val < (p.toFun i).val then 1 else 0) +
            (List.range (n' - k.val)).countP (fun r => if hr : k.val + 1 + r < n' + 1 then decide (i.val < k.val + 1 + r) && decide ((p.toFun ⟨k.val + 1 + r, hr⟩).val < (p.toFun i).val) else false) := by
          intro i
          rw [show (List.finRange (n' + 1)).countP (fun j => decide (i.val < j.val) && decide ((p.toFun j).val < (p.toFun i).val)) =
              (List.range (n' + 1)).countP (fun j => if hj : j < n' + 1 then decide (i.val < j) && decide ((p.toFun ⟨j, hj⟩).val < (p.toFun i).val) else false) by
            rw [← map_finRange_eq_range_countP (n' + 1)]
            apply List.countP_congr
            intro x _
            simp [x.isLt]]
          rw [countP_range_split_at n' k.val hk_le]
          congr 1
          congr 1
          simp only [(by omega : k.val < n' + 1), ↓reduceDIte]
          by_cases h1 : i.val < k.val <;> by_cases h2 : (p.toFun k).val < (p.toFun i).val <;> simp [h1, h2]
        have hfin_outer : sumNat (List.finRange (n' + 1)) (fun i => (List.finRange (n' + 1)).countP
            (fun j => decide (i.val < j.val) && decide ((p.toFun j).val < (p.toFun i).val))) =
            sumNat (List.finRange (n' + 1)) (fun i =>
              (List.range k.val).countP (fun j => if hj : j < n' + 1 then decide (i.val < j) && decide ((p.toFun ⟨j, hj⟩).val < (p.toFun i).val) else false)) +
            sumNat (List.finRange (n' + 1)) (fun i => if i.val < k.val ∧ (p.toFun k).val < (p.toFun i).val then 1 else 0) +
            sumNat (List.finRange (n' + 1)) (fun i =>
              (List.range (n' - k.val)).countP (fun r => if hr : k.val + 1 + r < n' + 1 then decide (i.val < k.val + 1 + r) && decide ((p.toFun ⟨k.val + 1 + r, hr⟩).val < (p.toFun i).val) else false)) := by
          rw [← sumNat_add, ← sumNat_add]
          apply sumNat_congr
          intro i _
          exact houter i
        -- Evaluate the 3 outer sums via sumNat_finRange_split_at
        have ht1 : sumNat (List.finRange (n' + 1)) (fun i =>
            (List.range k.val).countP (fun j => if hj : j < n' + 1 then decide (i.val < j) && decide ((p.toFun ⟨j, hj⟩).val < (p.toFun i).val) else false)) =
            pL.invCnt := by
          rw [sumNat_finRange_split_at n' k.val hk_le]
          have hmid : (List.range k.val).countP (fun j => if hj : j < n' + 1 then decide (k.val < j) && decide ((p.toFun ⟨j, hj⟩).val < (p.toFun ⟨k.val, by omega⟩).val) else false) = 0 := by
            rw [countP_eq_sumNat]
            refine (sumNat_congr (List.range k.val) _ _ fun j hj => ?_).trans (sumNat_zero (List.range k.val))
            rw [List.mem_range] at hj
            by_cases hjn : j < n' + 1
            · simp only [hjn, ↓reduceDIte, Bool.and_eq_true, decide_eq_true_eq]
              have hnot : ¬ (k.val < j ∧ (p.toFun ⟨j, hjn⟩).val < (p.toFun ⟨k.val, by omega⟩).val) := by omega
              simp [hnot]
            · simp [hjn]
          have hr0 : sumNat (List.range (n' - k.val)) (fun r => if hr : k.val + 1 + r < n' + 1 then
              (List.range k.val).countP (fun j => if hj : j < n' + 1 then decide (k.val + 1 + r < j) && decide ((p.toFun ⟨j, hj⟩).val < (p.toFun ⟨k.val + 1 + r, hr⟩).val) else false) else 0) = 0 := by
            refine (sumNat_congr (List.range (n' - k.val)) _ _ fun r _ => ?_).trans (sumNat_zero (List.range (n' - k.val)))
            split
            · rw [countP_eq_sumNat]
              refine (sumNat_congr (List.range k.val) _ _ fun j hj => ?_).trans (sumNat_zero (List.range k.val))
              rw [List.mem_range] at hj
              by_cases hjn : j < n' + 1
              · simp only [hjn, ↓reduceDIte, Bool.and_eq_true, decide_eq_true_eq]
                have hnot : ¬ (k.val + 1 + r < j ∧ (p.toFun ⟨j, hjn⟩).val < (p.toFun ⟨k.val + 1 + r, by assumption⟩).val) := by omega
                simp [hnot]
              · simp [hjn]
            · rfl
          rw [hmid, hr0]
          simp only [Nat.add_zero]
          unfold PermFin.invCnt
          symm
          apply sumNat_finRange_congr_range
          intro i
          have hi_lt := i.isLt
          have hni : i.val < n' + 1 := by omega
          simp only [hni, ↓reduceDIte]
          dsimp [pL]
          rw [← map_finRange_eq_range_countP k.val]
          apply List.countP_congr
          intro j _
          have hj_lt := j.isLt
          simp [(by omega : j.val < n' + 1)]
        have ht2 : sumNat (List.finRange (n' + 1)) (fun i => if i.val < k.val ∧ (p.toFun k).val < (p.toFun i).val then 1 else 0) = 0 := by
          refine (sumNat_congr (List.finRange (n' + 1)) _ _ fun i _ => ?_).trans (sumNat_zero (List.finRange (n' + 1)))
          have := (p.toFun i).isLt
          rw [hpk_val]
          have hnot : ¬ (i.val < k.val ∧ n' < (p.toFun i).val) := by omega
          simp [hnot]
        have ht3 : sumNat (List.finRange (n' + 1)) (fun i =>
            (List.range (n' - k.val)).countP (fun r => if hr : k.val + 1 + r < n' + 1 then decide (i.val < k.val + 1 + r) && decide ((p.toFun ⟨k.val + 1 + r, hr⟩).val < (p.toFun i).val) else false)) =
            pR.invCnt + (n' - k.val) := by
          rw [sumNat_finRange_split_at n' k.val hk_le]
          have hleft0 : sumNat (List.range k.val) (fun i => if hi : i < n' + 1 then
              (List.range (n' - k.val)).countP (fun r => if hr : k.val + 1 + r < n' + 1 then decide (i < k.val + 1 + r) && decide ((p.toFun ⟨k.val + 1 + r, hr⟩).val < (p.toFun ⟨i, hi⟩).val) else false) else 0) = 0 := by
            refine (sumNat_congr (List.range k.val) _ _ fun i hi => ?_).trans (sumNat_zero (List.range k.val))
            rw [List.mem_range] at hi
            simp only [(by omega : i < n' + 1), ↓reduceDIte]
            rw [countP_eq_sumNat]
            refine (sumNat_congr (List.range (n' - k.val)) _ _ fun r hr => ?_).trans (sumNat_zero (List.range (n' - k.val)))
            rw [List.mem_range] at hr
            have hri : k.val + 1 + r < n' + 1 := by omega
            have h1 := hleft_lt ⟨i, by omega⟩ hi
            have h2 := hright_ge ⟨k.val + 1 + r, hri⟩ (by dsimp; omega)
            simp only [hri, ↓reduceDIte, Bool.and_eq_true, decide_eq_true_eq]
            have hnot : ¬ (i < k.val + 1 + r ∧ (p.toFun ⟨k.val + 1 + r, hri⟩).val < (p.toFun ⟨i, by omega⟩).val) := by omega
            simp [hnot]
          have hmid_eq : (List.range (n' - k.val)).countP (fun r => if hr : k.val + 1 + r < n' + 1 then decide (k.val < k.val + 1 + r) && decide ((p.toFun ⟨k.val + 1 + r, hr⟩).val < (p.toFun ⟨k.val, by omega⟩).val) else false) = n' - k.val := by
            rw [countP_eq_sumNat]
            have h1 : ∀ r ∈ List.range (n' - k.val),
                (if (if hr : k.val + 1 + r < n' + 1 then decide (k.val < k.val + 1 + r) && decide ((p.toFun ⟨k.val + 1 + r, hr⟩).val < (p.toFun ⟨k.val, by omega⟩).val) else false) = true then 1 else 0) = 1 := by
              intro r hr; rw [List.mem_range] at hr
              have hri : k.val + 1 + r < n' + 1 := by omega
              have hlt_top := hright_lt ⟨k.val + 1 + r, hri⟩ (by dsimp; omega)
              have hk' : (⟨k.val, by omega⟩ : Fin (n' + 1)) = k := Fin.eta k _
              rw [hk', hpk_val]
              simp [hri, (by omega : k.val < k.val + 1 + r), hlt_top]
            rw [sumNat_congr (List.range (n' - k.val)) _ _ h1]
            clear hfin_outer houter ht1 ht2 hleft0
            induction (n' - k.val) with
            | zero => simp [sumNat]
            | succ t iht => rw [List.range_succ, sumNat_append, iht]; simp [sumNat]
          have hr_eq : sumNat (List.range (n' - k.val)) (fun s =>
              if hs : k.val + 1 + s < n' + 1 then
                (List.range (n' - k.val)).countP (fun r => if hr : k.val + 1 + r < n' + 1 then decide (k.val + 1 + s < k.val + 1 + r) && decide ((p.toFun ⟨k.val + 1 + r, hr⟩).val < (p.toFun ⟨k.val + 1 + s, hs⟩).val) else false)
              else 0) = pR.invCnt := by
            unfold PermFin.invCnt
            symm
            apply sumNat_finRange_congr_range
            intro s
            have hs_lt := s.isLt
            have hsi : k.val + 1 + s.val < n' + 1 := by omega
            simp only [hsi, ↓reduceDIte]
            dsimp [pR]
            rw [← map_finRange_eq_range_countP (n' - k.val)]
            apply List.countP_congr
            intro r _
            have hr_lt := r.isLt
            have hri : k.val + 1 + r.val < n' + 1 := by omega
            have hs_ge := hright_ge ⟨k.val + 1 + s.val, hsi⟩ (by dsimp; omega)
            have hr_ge := hright_ge ⟨k.val + 1 + r.val, hri⟩ (by dsimp; omega)
            simp only [hri, ↓reduceDIte]
            by_cases h1 : s.val < r.val <;> by_cases h2 : (p.toFun ⟨k.val + 1 + r.val, hri⟩).val < (p.toFun ⟨k.val + 1 + s.val, hsi⟩).val <;>
              simp [h1, h2, (by omega : (k.val + 1 + s.val < k.val + 1 + r.val) ↔ s.val < r.val)] <;> omega
          rw [hleft0, hmid_eq, hr_eq]
          omega
        rw [← hinv_lhs] at hfin_outer
        rw [hfin_outer, ht1, ht2, ht3]
        omega
      -- 2. Decompose p.disp2 + 2 * pR.excCnt = pL.disp2 + pR.disp2 + 2 * (n' - k.val)
      have hdisp_eq : p.disp2 + 2 * pR.excCnt = pL.disp2 + pR.disp2 + 2 * (n' - k.val) := by
        have hdisp_lhs : p.disp2 = sumNat (List.finRange (n' + 1)) (fun i => natAbsDiff (p.toFun i).val i.val) := rfl
        have hexc_lhs : pR.excCnt = (List.finRange (n' - k.val)).countP (fun r => decide (r.val < (pR.toFun r).val)) := rfl
        rw [hdisp_lhs, hexc_lhs]
        rw [sumNat_finRange_split_at n' k.val hk_le]
        have hL_part : sumNat (List.range k.val) (fun i => if hi : i < n' + 1 then natAbsDiff (p.toFun ⟨i, hi⟩).val i else 0) =
            pL.disp2 := by
          unfold PermFin.disp2
          symm
          apply sumNat_finRange_congr_range
          intro i
          have := i.isLt
          simp [(by omega : i.val < n' + 1), pL]
        have hmid_part : natAbsDiff (p.toFun ⟨k.val, by omega⟩).val k.val = n' - k.val := by
          have hk' : (⟨k.val, by omega⟩ : Fin (n' + 1)) = k := Fin.eta k _
          rw [hk', hpk_val]
          unfold natAbsDiff
          split <;> omega
        have hsum_exc : sumNat (List.finRange (n' - k.val))
            (fun r => natAbsDiff (k.val + (pR.toFun r).val) (k.val + 1 + r.val) +
                      2 * (if r.val < (pR.toFun r).val then 1 else 0)) =
            sumNat (List.finRange (n' - k.val)) (fun r => natAbsDiff (pR.toFun r).val r.val + 1) := by
          apply sumNat_congr
          intro r _
          unfold natAbsDiff
          by_cases hr : r.val < (pR.toFun r).val
          · simp [hr]; split <;> split <;> omega
          · simp [hr]; split <;> split <;> omega
        have hR_sum1 : sumNat (List.finRange (n' - k.val)) (fun _ => 1) = n' - k.val := by
          have hz : sumNat (List.range (n' - k.val)) (fun _ => 1) = n' - k.val := by
            induction (n' - k.val) with
            | zero => rfl
            | succ t iht => rw [List.range_succ, sumNat_append, iht]; simp [sumNat]
          rw [sumNat_finRange_eq_range (n' - k.val) (fun _ => 1), hz]
        have hR_disp : sumNat (List.range (n' - k.val)) (fun r => if hr : k.val + 1 + r < n' + 1 then
              natAbsDiff (p.toFun ⟨k.val + 1 + r, hr⟩).val (k.val + 1 + r) else 0) =
            sumNat (List.finRange (n' - k.val)) (fun r => natAbsDiff (k.val + (pR.toFun r).val) (k.val + 1 + r.val)) := by
          symm
          apply sumNat_finRange_congr_range
          intro r
          have hr_lt := r.isLt
          have hri : k.val + 1 + r.val < n' + 1 := by omega
          have hge := hright_ge ⟨k.val + 1 + r.val, hri⟩ (by dsimp; omega)
          simp only [hri, ↓reduceDIte, pR]
          congr 1
          omega
        have hexc_eq : 2 * (List.finRange (n' - k.val)).countP (fun r => decide (r.val < (pR.toFun r).val)) =
            sumNat (List.finRange (n' - k.val)) (fun r => 2 * (if r.val < (pR.toFun r).val then 1 else 0)) := by
          rw [countP_eq_sumNat, sumNat_const_mul]
          apply sumNat_congr
          intro r _
          by_cases hr : r.val < (pR.toFun r).val <;> simp [hr]
        rw [hL_part, hmid_part, hR_disp, hexc_eq]
        have hadd1 : sumNat (List.finRange (n' - k.val)) (fun r => natAbsDiff (k.val + (pR.toFun r).val) (k.val + 1 + r.val)) +
            sumNat (List.finRange (n' - k.val)) (fun r => 2 * (if r.val < (pR.toFun r).val then 1 else 0)) =
            pR.disp2 + (n' - k.val) := by
          unfold PermFin.disp2
          rw [← sumNat_add, hsum_exc, sumNat_add, hR_sum1]
        omega
      -- 3. Decompose p.toList and desList p.toList
      have hp_list_eq : p.toList = pL.toList ++ [n'] ++ pR.toList.map (· + k.val) := by
        have hsplit_r := range_split_at n' k.val hk_le
        let g : Nat → Nat := fun i => if hi : i < n' + 1 then (p.toFun ⟨i, hi⟩).val else 0
        have htg : p.toList = (List.range (n' + 1)).map g := by
          unfold PermFin.toList
          rw [← finRange_map_val (n' + 1), List.map_map]
          apply List.map_congr_left
          intro i _
          simp only [Function.comp_def, g, i.isLt, ↓reduceDIte]
        have hm1 : (List.range k.val).map g =
            (List.finRange k.val).map (fun i => (pL.toFun i).val) := by
          rw [← finRange_map_val k.val, List.map_map]
          apply List.map_congr_left
          intro i _
          have := i.isLt
          simp only [Function.comp_def, g, (by omega : i.val < n' + 1), ↓reduceDIte, pL]
        have hm_k : g k.val = n' := by
          simp [g, k.isLt, hpk_val]
        have hm2 : ((List.range (n' - k.val)).map (k.val + 1 + ·)).map g =
            ((List.finRange (n' - k.val)).map (fun j => (pR.toFun j).val)).map (· + k.val) := by
          rw [List.map_map, ← finRange_map_val (n' - k.val), List.map_map, List.map_map]
          apply List.map_congr_left
          intro r _
          have hr_lt := r.isLt
          have hri : k.val + 1 + r.val < n' + 1 := by omega
          have hge := hright_ge ⟨k.val + 1 + r.val, hri⟩ (by dsimp; omega)
          simp only [Function.comp_def, g, hri, ↓reduceDIte, pR]
          omega
        rw [htg, hsplit_r, List.map_append, List.map_cons, hm1, hm_k, hm2]
        simp [PermFin.toList, List.append_assoc]
      have hL_lt_top : ∀ x ∈ pL.toList, x < n' := by
        intro x hx
        unfold PermFin.toList at hx
        rw [List.mem_map] at hx
        rcases hx with ⟨i, _, rfl⟩
        have := (pL.toFun i).isLt
        omega
      cases hnmk : n' - k.val with
      | zero =>
        have hr_inv : pR.invCnt = 0 := permFin_zero_invCnt hnmk pR
        have hr_disp : pR.disp2 = 0 := permFin_zero_disp2 hnmk pR
        have hr_exc : pR.excCnt = 0 := permFin_zero_excCnt hnmk pR
        have hr_list : pR.toList = [] := permFin_zero_toList hnmk pR
        have hdes_eq : desList p.toList = desList pL.toList := by
          rw [hp_list_eq, hr_list, List.map_nil, List.append_nil]
          exact desList_append_last_lt pL.toList n' hL_lt_top
        have ihL := ih k.val (by omega) pL hL231
        rw [hdes_eq]
        omega
      | succ r' =>
        have hR_ne : pR.toList ≠ [] := permFin_succ_toList_ne hnmk pR
        cases hRl : pR.toList with
        | nil => exact False.elim (hR_ne hRl)
        | cons b_val bs =>
          have hmem_b : b_val ∈ pR.toList := by rw [hRl]; simp
          have hb_lt : b_val < n' - k.val := by
            unfold PermFin.toList at hmem_b
            rw [List.mem_map] at hmem_b
            rcases hmem_b with ⟨j, _, rfl⟩
            exact (pR.toFun j).isLt
          have hR_mapped : pR.toList.map (· + k.val) = (b_val + k.val) :: bs.map (· + k.val) := by
            rw [hRl, List.map_cons]
          have hn_gt_b : n' > b_val + k.val := by omega
          have hdes_eq : desList p.toList = desList pL.toList + 1 + desList pR.toList := by
            rw [hp_list_eq, List.append_assoc, hR_mapped]
            simp only [List.cons_append, List.nil_append]
            rw [desList_append_split pL.toList (bs.map (· + k.val)) n' (b_val + k.val) hL_lt_top hn_gt_b]
            have hm_add : desList ((b_val + k.val) :: bs.map (· + k.val)) = desList pR.toList := by
              rw [← hR_mapped, desList_map_add]
            rw [hm_add]
          have ihL := ih k.val (by omega) pL hL231
          have ihR := ih (n' - k.val) (by omega) pR hR231
          have hexcR := avoids231_exc_le_des pR hR231
          let dL := desList pL.toList
          let dR := desList pR.toList
          change 2 * pL.invCnt ≤ pL.disp2 + dL * (dL + 1) at ihL
          change 2 * pR.invCnt ≤ pR.disp2 + dR * (dR + 1) at ihR
          change pR.excCnt ≤ dR at hexcR
          have halg := des_quad_le dL dR
          have hcomb : 2 * pL.invCnt + 2 * pR.invCnt ≤
              (pL.disp2 + pR.disp2) + (dL * (dL + 1) + dR * (dR + 1)) := by omega
          have hexc2 : 2 * pR.excCnt ≤ 2 * dR := Nat.mul_le_mul_left 2 hexcR
          rw [hdes_eq]
          change 2 * p.invCnt ≤ p.disp2 + (dL + 1 + dR) * (dL + 1 + dR + 1)
          omega

theorem avoids231_two_inv_le_disp2_add_des {n : Nat} (p : PermFin n) (h231 : p.Avoids231) :
    2 * p.invCnt ≤ p.disp2 + desList p.toList * (desList p.toList + 1) :=
  avoids231_two_inv_aux n n (Nat.le_refl n) p h231

end PermFin

-- ============================================================================
-- Theorem 5: Mantel's Theorem & Triangle-Free m <= nu * (n - nu)
-- ============================================================================

namespace SimpleGraphFin

private theorem sg_sumNat_zero {α : Type} (xs : List α) : sumNat xs (fun _ => 0) = 0 := by
  induction xs <;> simp [sumNat, *]

private theorem sg_nodup_filter {α : Type} (P : α → Bool) {xs : List α} (h : xs.Nodup) :
    (xs.filter P).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    rw [List.nodup_cons] at h
    simp only [List.filter_cons]
    cases hpx : P x
    · exact ih h.2
    · simp only [↓reduceIte, List.nodup_cons]
      refine ⟨fun hm => h.1 ((List.mem_filter.mp hm).1), ih h.2⟩

private theorem two_mul_le_sq_add_sq (a b : Nat) : 2 * a * b ≤ a * a + b * b := by
  by_cases h : a ≤ b
  · rcases Nat.exists_eq_add_of_le h with ⟨d, rfl⟩
    have hcm : d * a = a * d := Nat.mul_comm d a
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, hcm]
    omega
  · have hba : b ≤ a := Nat.le_of_not_le h
    rcases Nat.exists_eq_add_of_le hba with ⟨d, rfl⟩
    have hcm : d * b = b * d := Nat.mul_comm d b
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, hcm]
    omega

private theorem two_mul_mul_sumNat_le {α : Type} (a : Nat) (xs : List α) (g : α → Nat) :
    2 * a * sumNat xs g ≤ xs.length * (a * a) + sumNat xs (fun y => g y * g y) := by
  induction xs with
  | nil => simp [sumNat]
  | cons y rest ih =>
    simp only [sumNat, List.length_cons]
    have hxy := two_mul_le_sq_add_sq a (g y)
    have hmul : 2 * a * (g y + sumNat rest g) = 2 * a * g y + 2 * a * sumNat rest g := Nat.mul_add _ _ _
    have hlen : (rest.length + 1) * (a * a) = rest.length * (a * a) + a * a := by
      simp only [Nat.add_mul, Nat.one_mul]
    omega

private theorem sumNat_sq_le_length_mul {α : Type} (xs : List α) (f : α → Nat) :
    sumNat xs f * sumNat xs f ≤ xs.length * sumNat xs (fun x => f x * f x) := by
  induction xs with
  | nil => simp [sumNat]
  | cons x rest ih =>
    simp only [sumNat, List.length_cons]
    have hcross := two_mul_mul_sumNat_le (f x) rest f
    have hcm : sumNat rest f * f x = f x * sumNat rest f := Nat.mul_comm _ _
    have hlhs : (f x + sumNat rest f) * (f x + sumNat rest f) =
        f x * f x + 2 * f x * sumNat rest f + sumNat rest f * sumNat rest f := by
      simp only [Nat.add_mul, Nat.mul_add, hcm, Nat.mul_assoc]
      omega
    have hrhs : (rest.length + 1) * (f x * f x + sumNat rest (fun y => f y * f y)) =
        f x * f x + rest.length * (f x * f x) + sumNat rest (fun y => f y * f y) +
        rest.length * sumNat rest (fun y => f y * f y) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
      omega
    omega

private theorem sumNat_mem_nodup {α : Type} [DecidableEq α] (xs S : List α)
    (hnx : xs.Nodup) (hnS : S.Nodup) (hsub : ∀ s ∈ S, s ∈ xs) (f : α → Nat) :
    sumNat xs (fun x => if x ∈ S then f x else 0) = sumNat S f := by
  induction S with
  | nil =>
    exact sg_sumNat_zero xs
  | cons a rest ih =>
    rw [List.nodup_cons] at hnS
    have hind := sumNat_eq_indicator_one xs hnx a (hsub a (by simp))
    have hfa : sumNat xs (fun x => if x = a then f x else 0) = f a := by
      have hm := sumNat_const_mul (f a) xs (fun x => if x = a then 1 else 0)
      rw [hind, Nat.mul_one] at hm
      rw [hm]
      apply sumNat_congr
      intro x _
      by_cases hx : x = a
      · subst hx; simp
      · simp [hx]
    have ihr := ih hnS.2 (fun s hs => hsub s (by simp [hs]))
    simp only [sumNat, ← ihr, ← hfa, ← sumNat_add]
    apply sumNat_congr
    intro x _
    by_cases hxa : x = a
    · subst hxa; simp [hnS.1]
    · by_cases hxr : x ∈ rest <;> simp [hxa, hxr]

private theorem sumNat_filter_eq {α : Type} (xs : List α) (Q : α → Bool) (f : α → Nat) :
    sumNat (xs.filter Q) f = sumNat xs (fun x => if Q x = true then f x else 0) := by
  induction xs with
  | nil => simp [sumNat]
  | cons x rest ih =>
    simp only [List.filter_cons]
    cases hqx : Q x <;> simp [sumNat, hqx, ih]

private theorem sumNat_const_one {α : Type} (xs : List α) :
    sumNat xs (fun _ => 1) = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ rest ih => simp [sumNat, ih]; omega

private theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] (S xs : List α)
    (hS : S.Nodup) (hx : xs.Nodup) (hsub : ∀ s ∈ S, s ∈ xs) :
    S.length ≤ xs.length := by
  have h1 : S.length = xs.countP (fun x => decide (x ∈ S)) := by
    rw [countP_eq_sumNat]
    have hm := sumNat_mem_nodup xs S hx hS hsub (fun _ => 1)
    rw [sumNat_const_one] at hm
    rw [← hm]
    apply sumNat_congr
    intro x _
    by_cases hxS : x ∈ S <;> simp [hxS]
  rw [h1, countP_eq_sumNat, ← sumNat_const_one xs]
  apply sumNat_mono
  intro x _
  split <;> omega

private theorem triangleFree_not_tri {n : Nat} {G : SimpleGraphFin n} (hTF : G.TriangleFree)
    {u v w : Fin n} (h1 : G.adj u v = true) (h2 : G.adj v w = true) (h3 : G.adj u w = true) : False := by
  have hh := hTF u v w
  simp [h1, h2, h3] at hh

private theorem c4Free_not_cycle {n : Nat} {G : SimpleGraphFin n} (hC4 : G.C4Free) {a b c d : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h1 : G.adj a b = true) (h2 : G.adj b c = true) (h3 : G.adj c d = true) (h4 : G.adj d a = true) : False := by
  have hh := hC4 a b c d hab hac had hbc hbd hcd
  simp [h1, h2, h3, h4] at hh

private theorem two_mul_edgeCount {n : Nat} (G : SimpleGraphFin n) :
    2 * G.edgeCount = sumNat (List.finRange n) (fun u =>
      sumNat (List.finRange n) (fun v => if G.adj u v = true then 1 else 0)) := by
  let f : Fin n → Fin n → Nat := fun u v => if G.adj u v = true then 1 else 0
  have hsymm : ∀ u v, f u v = f v u := fun u v => by simp [f, G.symm u v]
  have hdiag : ∀ u, f u u = 0 := fun u => by simp [f, G.loopless]
  have he : G.edgeCount = sumNat (List.finRange n) (fun u =>
      sumNat (List.finRange n) (fun v => if u.val < v.val then f u v else 0)) := by
    unfold edgeCount
    apply sumNat_congr
    intro u _
    rw [countP_eq_sumNat]
    apply sumNat_congr
    intro v _
    by_cases huv : u.val < v.val <;> by_cases ha : G.adj u v = true <;> simp [f, huv, ha]
  rw [he]
  exact two_mul_sumNat_fin_lt f hsymm hdiag

theorem mantel_sublist {n : Nat} (G : SimpleGraphFin n) (hTF : G.TriangleFree)
    (S : List (Fin n)) (hS : S.Nodup) :
    2 * sumNat S (fun u => S.countP (fun v => G.adj u v)) ≤ S.length * S.length := by
  let _ := hS
  let degS : Fin n → Nat := fun u => S.countP (fun v => G.adj u v)
  let two_mS := sumNat S degS
  have hadj_sum : ∀ u v : Fin n, G.adj u v = true → degS u + degS v ≤ S.length := by
    intro u v huv
    dsimp [degS]
    rw [countP_eq_sumNat, countP_eq_sumNat, ← sumNat_add, ← sumNat_const_one S]
    apply sumNat_mono
    intro w _
    cases huw : G.adj u w <;> cases hvw : G.adj v w <;> simp
    exact False.elim (triangleFree_not_tri hTF huv hvw huw)
  have hdeg_sq : ∀ u : Fin n, degS u * degS u =
      sumNat S (fun v => if G.adj u v = true then degS u else 0) := by
    intro u
    have hd : degS u = sumNat S (fun v => if G.adj u v = true then 1 else 0) := by
      dsimp [degS]; rw [countP_eq_sumNat]
    have hmul := sumNat_const_mul (degS u) S (fun v => if G.adj u v = true then 1 else 0)
    rw [show degS u * degS u = degS u * sumNat S (fun v => if G.adj u v = true then 1 else 0) by rw [← hd]]
    rw [hmul]
    apply sumNat_congr
    intro v _
    cases G.adj u v <;> simp
  have hsum_sq_eq : 2 * sumNat S (fun u => degS u * degS u) =
      sumNat S (fun u => sumNat S (fun v => if G.adj u v = true then degS u + degS v else 0)) := by
    have h1 : sumNat S (fun u => degS u * degS u) =
        sumNat S (fun u => sumNat S (fun v => if G.adj u v = true then degS u else 0)) :=
      sumNat_congr S _ _ (fun u _ => hdeg_sq u)
    have hswap : sumNat S (fun u => sumNat S (fun v => if G.adj u v = true then degS u else 0)) =
        sumNat S (fun u => sumNat S (fun v => if G.adj u v = true then degS v else 0)) := by
      rw [sumNat_swap]
      apply sumNat_congr
      intro v _
      apply sumNat_congr
      intro u _
      rw [G.symm]
    have hadd : sumNat S (fun u => sumNat S (fun v => if G.adj u v = true then degS u else 0)) +
        sumNat S (fun u => sumNat S (fun v => if G.adj u v = true then degS v else 0)) =
        sumNat S (fun u => sumNat S (fun v => if G.adj u v = true then degS u + degS v else 0)) := by
      rw [← sumNat_add]
      apply sumNat_congr
      intro u _
      rw [← sumNat_add]
      apply sumNat_congr
      intro v _
      cases G.adj u v <;> simp
    omega
  have hsum_sq_ub : 2 * sumNat S (fun u => degS u * degS u) ≤ S.length * two_mS := by
    rw [hsum_sq_eq]
    have hmono : sumNat S (fun u => sumNat S (fun v => if G.adj u v = true then degS u + degS v else 0)) ≤
        sumNat S (fun u => sumNat S (fun v => if G.adj u v = true then S.length else 0)) := by
      apply sumNat_mono
      intro u _
      apply sumNat_mono
      intro v _
      by_cases huv : G.adj u v = true
      · simp only [huv, ↓reduceIte]; exact hadj_sum u v huv
      · simp [huv]
    have hrhs : S.length * two_mS =
        sumNat S (fun u => sumNat S (fun v => if G.adj u v = true then S.length else 0)) := by
      dsimp [two_mS, degS]
      rw [sumNat_const_mul]
      apply sumNat_congr
      intro u _
      rw [countP_eq_sumNat, sumNat_const_mul]
      apply sumNat_congr
      intro v _
      cases G.adj u v <;> simp
    omega
  have hcs := sumNat_sq_le_length_mul S degS
  change two_mS * two_mS ≤ S.length * sumNat S (fun x => degS x * degS x) at hcs
  have hquad : 2 * two_mS * two_mS ≤ S.length * S.length * two_mS := by
    calc 2 * two_mS * two_mS
        = 2 * (two_mS * two_mS) := Nat.mul_assoc _ _ _
      _ ≤ 2 * (S.length * sumNat S (fun x => degS x * degS x)) := Nat.mul_le_mul_left 2 hcs
      _ = S.length * (2 * sumNat S (fun x => degS x * degS x)) := Nat.mul_left_comm 2 S.length _
      _ ≤ S.length * (S.length * two_mS) := Nat.mul_le_mul_left S.length hsum_sq_ub
      _ = S.length * S.length * two_mS := (Nat.mul_assoc _ _ _).symm
  by_cases hm0 : two_mS = 0
  · change 2 * two_mS ≤ S.length * S.length
    rw [hm0]; simp
  · have hm_pos : 0 < two_mS := Nat.pos_of_ne_zero hm0
    exact Nat.le_of_mul_le_mul_right hquad hm_pos

theorem mantel_triangleFree {n : Nat} (G : SimpleGraphFin n) (hTF : G.TriangleFree) :
    4 * G.edgeCount ≤ n * n := by
  have h := mantel_sublist G hTF (List.finRange n) (List.nodup_finRange n)
  rw [@List.length_finRange n] at h
  have h2m : 2 * G.edgeCount = sumNat (List.finRange n) (fun u => (List.finRange n).countP (fun v => G.adj u v)) := by
    rw [two_mul_edgeCount]
    apply sumNat_congr
    intro u _
    rw [countP_eq_sumNat]
  rw [← h2m] at h
  omega

def ordEdge {n : Nat} (u v : Fin n) : Fin n × Fin n :=
  if u.val < v.val then (u, v) else (v, u)

private theorem mem_ordEdge_iff {n : Nat} (a b z : Fin n) :
    z ∈ [(ordEdge a b).1, (ordEdge a b).2] ↔ z = a ∨ z = b := by
  unfold ordEdge
  by_cases h : a.val < b.val
  · simp [h]
  · simp only [h, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨fun h' => h'.elim Or.inr Or.inl, fun h' => h'.elim Or.inr Or.inl⟩

private theorem flatMap_pair_length {α : Type} (xs : List (α × α)) :
    (xs.flatMap (fun e => [e.1, e.2])).length = 2 * xs.length := by
  induction xs with
  | nil => simp
  | cons _ rest ih => simp [List.flatMap_cons, List.length_cons, ih]; omega

private theorem sumNat_flatMap_pair {α : Type} (xs : List (α × α)) (f : α → Nat) :
    sumNat (xs.flatMap (fun e => [e.1, e.2])) f = sumNat xs (fun e => f e.1 + f e.2) := by
  induction xs with
  | nil => simp [sumNat]
  | cons e rest ih => simp [List.flatMap_cons, sumNat, ih]; omega

theorem triangleFree_edgeCount_le_matching {n : Nat} (G : SimpleGraphFin n) (k : Nat)
    (hTF : G.TriangleFree) (hM : G.MatchingNum k) :
    G.edgeCount ≤ k * (n - k) := by
  rcases hM with ⟨⟨M, hIsM, hlenM⟩, hMaxM⟩
  let VM := M.flatMap (fun e => [e.1, e.2])
  have hVM_nodup : VM.Nodup := hIsM.2
  have hVM_len : VM.length = 2 * k := by
    dsimp [VM]; rw [flatMap_pair_length, hlenM]
  have h2kn : 2 * k ≤ n := by
    calc 2 * k = VM.length := hVM_len.symm
      _ ≤ (List.finRange n).length := length_le_of_nodup_subset VM (List.finRange n) hVM_nodup (List.nodup_finRange n) (fun x _ => List.mem_finRange x)
      _ = n := List.length_finRange
  let U := (List.finRange n).filter (fun v => !decide (v ∈ VM))
  have hU_nodup : U.Nodup := sg_nodup_filter _ (List.nodup_finRange n)
  have hU_len : U.length = n - 2 * k := by
    have htot : sumNat (List.finRange n) (fun _ => 1) =
        sumNat (List.finRange n) (fun v => if v ∈ VM then 1 else 0) +
        sumNat (List.finRange n) (fun v => if (!decide (v ∈ VM)) = true then 1 else 0) := by
      rw [← sumNat_add]
      apply sumNat_congr
      intro v _
      by_cases hv : v ∈ VM <;> simp [hv]
    rw [sumNat_const_one, @List.length_finRange n,
        sumNat_mem_nodup (List.finRange n) VM (List.nodup_finRange n) hVM_nodup (fun x _ => List.mem_finRange x) (fun _ => 1),
        sumNat_const_one, hVM_len, ← sumNat_filter_eq, sumNat_const_one] at htot
    change n = 2 * k + U.length at htot
    omega
  have hU_indep : ∀ u ∈ U, ∀ v ∈ U, G.adj u v = false := by
    intro u hu v hv
    apply Classical.byContradiction
    intro hne
    have huv : G.adj u v = true := by
      cases h : G.adj u v
      · exact False.elim (hne h)
      · rfl
    have hne_uv : u ≠ v := fun heq => by subst heq; rw [G.loopless] at huv; simp at huv
    rw [List.mem_filter] at hu hv
    have hu_not : u ∉ VM := by simpa using hu.2
    have hv_not : v ∉ VM := by simpa using hv.2
    let e0 := ordEdge u v
    have he0_spec : e0.1.val < e0.2.val ∧ G.adj e0.1 e0.2 = true := by
      dsimp [e0, ordEdge]
      by_cases hlt : u.val < v.val
      · simp [hlt, huv]
      · have hv_lt : v.val < u.val := by
          have : u.val ≠ v.val := fun h => hne_uv (Fin.ext h)
          omega
        simp [hlt, hv_lt, G.symm v u, huv]
    have hnew_M : G.IsMatching (e0 :: M) := by
      constructor
      · intro e he
        rcases List.mem_cons.mp he with rfl | hm
        · exact he0_spec
        · exact hIsM.1 e hm
      · rw [List.flatMap_cons]
        have h1 : e0.1 ∉ VM := by dsimp [e0, ordEdge]; split <;> assumption
        have h2 : e0.2 ∉ VM := by dsimp [e0, ordEdge]; split <;> assumption
        have h12 : e0.1 ≠ e0.2 := fun h => by have := he0_spec.1; rw [h] at this; omega
        rw [List.cons_append, List.cons_append, List.nil_append, List.nodup_cons, List.nodup_cons]
        refine ⟨fun hm => ?_, h2, hVM_nodup⟩
        rcases List.mem_cons.mp hm with heq | hm'
        · exact h12 heq
        · exact h1 hm'
    have hbad := hMaxM (e0 :: M) hnew_M
    simp [hlenM] at hbad
    omega
  -- Partition 2 * edgeCount over (VM ∪ U) x (VM ∪ U)
  have hpart_row : ∀ f : Fin n → Nat,
      sumNat (List.finRange n) f = sumNat VM f + sumNat U f := by
    intro f
    have hsplit : sumNat (List.finRange n) f =
        sumNat (List.finRange n) (fun x => if x ∈ VM then f x else 0) +
        sumNat (List.finRange n) (fun x => if (!decide (x ∈ VM)) = true then f x else 0) := by
      rw [← sumNat_add]
      apply sumNat_congr
      intro x _
      by_cases hx : x ∈ VM <;> simp [hx]
    rw [hsplit, sumNat_mem_nodup (List.finRange n) VM (List.nodup_finRange n) hVM_nodup (fun x _ => List.mem_finRange x) f,
        ← sumNat_filter_eq]
  have h2m_split : 2 * G.edgeCount =
      sumNat VM (fun u => sumNat VM (fun v => if G.adj u v = true then 1 else 0)) +
      sumNat VM (fun u => sumNat U (fun v => if G.adj u v = true then 1 else 0)) +
      sumNat U (fun u => sumNat VM (fun v => if G.adj u v = true then 1 else 0)) +
      sumNat U (fun u => sumNat U (fun v => if G.adj u v = true then 1 else 0)) := by
    rw [two_mul_edgeCount, hpart_row]
    have hA : sumNat VM (fun u => sumNat (List.finRange n) (fun v => if G.adj u v = true then 1 else 0)) =
        sumNat VM (fun u => sumNat VM (fun v => if G.adj u v = true then 1 else 0)) +
        sumNat VM (fun u => sumNat U (fun v => if G.adj u v = true then 1 else 0)) := by
      rw [← sumNat_add]
      apply sumNat_congr
      intro u _
      exact hpart_row _
    have hB : sumNat U (fun u => sumNat (List.finRange n) (fun v => if G.adj u v = true then 1 else 0)) =
        sumNat U (fun u => sumNat VM (fun v => if G.adj u v = true then 1 else 0)) +
        sumNat U (fun u => sumNat U (fun v => if G.adj u v = true then 1 else 0)) := by
      rw [← sumNat_add]
      apply sumNat_congr
      intro u _
      exact hpart_row _
    rw [hA, hB]
    omega
  have hUU : sumNat U (fun u => sumNat U (fun v => if G.adj u v = true then 1 else 0)) = 0 := by
    have h1 : ∀ u ∈ U, sumNat U (fun v => if G.adj u v = true then 1 else 0) = 0 := by
      intro u hu
      have h2 : ∀ v ∈ U, (if G.adj u v = true then 1 else 0) = 0 := by
        intro v hv
        simp [hU_indep u hu v hv]
      rw [sumNat_congr U _ _ h2, sg_sumNat_zero]
    rw [sumNat_congr U _ _ h1, sg_sumNat_zero]
  have hUV : sumNat U (fun u => sumNat VM (fun v => if G.adj u v = true then 1 else 0)) =
      sumNat VM (fun u => sumNat U (fun v => if G.adj u v = true then 1 else 0)) := by
    rw [sumNat_swap]
    apply sumNat_congr
    intro v _
    apply sumNat_congr
    intro u _
    rw [G.symm]
  have hVV : sumNat VM (fun u => sumNat VM (fun v => if G.adj u v = true then 1 else 0)) ≤ 2 * k * k := by
    have hm := mantel_sublist G hTF VM hVM_nodup
    rw [hVM_len] at hm
    have heq : sumNat VM (fun u => VM.countP (fun v => G.adj u v)) =
        sumNat VM (fun u => sumNat VM (fun v => if G.adj u v = true then 1 else 0)) := by
      apply sumNat_congr; intro u _; rw [countP_eq_sumNat]
    rw [heq] at hm
    have h4 : (2 * k) * (2 * k) = 2 * (2 * k * k) := by
      rw [Nat.mul_assoc 2 k (2 * k), Nat.mul_left_comm k 2 k, ← Nat.mul_assoc 2 k k]
    omega
  have hVU : sumNat VM (fun u => sumNat U (fun v => if G.adj u v = true then 1 else 0)) ≤ k * (n - 2 * k) := by
    have hflat : sumNat VM (fun u => sumNat U (fun v => if G.adj u v = true then 1 else 0)) =
        sumNat M (fun e =>
          sumNat U (fun v => if G.adj e.1 v = true then 1 else 0) +
          sumNat U (fun v => if G.adj e.2 v = true then 1 else 0)) :=
      sumNat_flatMap_pair M _
    rw [hflat]
    have hconst : sumNat M (fun _ => U.length) = k * (n - 2 * k) := by
      have hm := sumNat_const_mul U.length M (fun _ => 1)
      rw [sumNat_const_one, hlenM, hU_len] at hm
      simp only [Nat.mul_one] at hm
      rw [Nat.mul_comm] at hm
      rw [hU_len]
      exact hm.symm
    rw [← hconst]
    apply sumNat_mono
    intro e he
    have hadje : G.adj e.1 e.2 = true := (hIsM.1 e he).2
    rw [← sumNat_add, ← sumNat_const_one U]
    apply sumNat_mono
    intro w _
    cases hw1 : G.adj e.1 w <;> cases hw2 : G.adj e.2 w <;> simp
    exact False.elim (triangleFree_not_tri hTF hadje hw2 hw1)
  have hfin : 2 * G.edgeCount ≤ 2 * k * k + 2 * (k * (n - 2 * k)) := by
    rw [h2m_split, hUU, hUV]
    omega
  rcases Nat.exists_eq_add_of_le h2kn with ⟨d, hd⟩
  have h1 : n - 2 * k = d := by omega
  have h2 : n - k = k + d := by omega
  rw [h1] at hfin
  rw [h2]
  have hscaled : 2 * G.edgeCount ≤ 2 * (k * (k + d)) := by
    calc 2 * G.edgeCount
        ≤ 2 * k * k + 2 * (k * d) := hfin
      _ = 2 * (k * k) + 2 * (k * d) := by rw [Nat.mul_assoc]
      _ = 2 * (k * k + k * d) := (Nat.mul_add 2 (k * k) (k * d)).symm
      _ = 2 * (k * (k + d)) := by rw [← Nat.mul_add k k d]
  exact Nat.le_of_mul_le_mul_left hscaled (by omega : 0 < 2)

-- ============================================================================
-- Theorem 6: Connected C4-Free (n >= 4) min_deg <= MatchingNum
-- ============================================================================

private theorem foldl_min_le {α : Type} (f : α → Nat) (xs : List α) (init : Nat) :
    xs.foldl (fun acc w => min acc (f w)) init ≤ init ∧
    ∀ x ∈ xs, xs.foldl (fun acc w => min acc (f w)) init ≤ f x := by
  induction xs generalizing init with
  | nil =>
    exact ⟨Nat.le_refl _, fun _ h => by simp at h⟩
  | cons y rest ih =>
    rcases ih (min init (f y)) with ⟨h1, h2⟩
    refine ⟨Nat.le_trans h1 (Nat.min_le_left _ _), ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hr
    · exact Nat.le_trans h1 (Nat.min_le_right _ _)
    · exact h2 x hr

theorem minDeg_le_deg {n : Nat} (G : SimpleGraphFin n) (hn : 0 < n) (v : Fin n) :
    G.minDeg ≤ G.deg v := by
  unfold minDeg
  cases hr : List.finRange n with
  | nil =>
    have hl := @List.length_finRange n
    rw [hr] at hl
    simp at hl
    omega
  | cons w ws =>
    have hmem : v ∈ w :: ws := by rw [← hr]; exact List.mem_finRange v
    have hfl := foldl_min_le G.deg ws (G.deg w)
    rcases List.mem_cons.mp hmem with rfl | hws
    · exact hfl.1
    · exact hfl.2 v hws

private theorem exists_of_countP_pos {α : Type} (xs : List α) (P : α → Bool)
    (hpos : 0 < xs.countP P) : ∃ x ∈ xs, P x = true := by
  cases hf : xs.filter P with
  | nil =>
    have hc : (xs.filter P).length = xs.countP P := by
      clear hf hpos; induction xs <;> simp [List.filter_cons, List.countP_cons] <;> split <;> simp [*] <;> omega
    rw [hf] at hc; simp at hc; omega
  | cons x _ =>
    have hx : x ∈ xs.filter P := by rw [hf]; simp
    rw [List.mem_filter] at hx
    exact ⟨x, hx.1, hx.2⟩

private theorem two_of_countP_ge_two {α : Type} (xs : List α) (hnd : xs.Nodup) (P : α → Bool)
    (hge : 2 ≤ xs.countP P) : ∃ a ∈ xs, ∃ b ∈ xs, a ≠ b ∧ P a = true ∧ P b = true := by
  induction xs with
  | nil => simp at hge
  | cons x rest ih =>
    rw [List.nodup_cons] at hnd
    have hcons : (x :: rest).countP P = (if P x = true then 1 else 0) + rest.countP P := by
      rw [countP_eq_sumNat, sumNat, countP_eq_sumNat]
    rw [hcons] at hge
    by_cases hpx : P x = true
    · have hif1 : (if P x = true then 1 else 0) = 1 := by simp [hpx]
      rw [hif1] at hge
      have hpos : 0 < rest.countP P := by omega
      rcases exists_of_countP_pos rest P hpos with ⟨b, hb, hpb⟩
      have hne : x ≠ b := fun h => hnd.1 (h ▸ hb)
      exact ⟨x, by simp, b, by simp [hb], hne, hpx, hpb⟩
    · have hif0 : (if P x = true then 1 else 0) = 0 := by simp [hpx]
      rw [hif0] at hge
      rcases ih hnd.2 (by omega) with ⟨a, ha, b, hb, hne, hpa, hpb⟩
      exact ⟨a, by simp [ha], b, by simp [hb], hne, hpa, hpb⟩

private theorem walk_leaves_set {n : Nat} (G : SimpleGraphFin n) (S : List (Fin n))
    (walk : List (Fin n)) (hs : ∀ s, walk.head? = some s → s ∈ S)
    (ht : ∀ t, walk.getLast? = some t → t ∉ S) (hw : G.IsWalk walk) (hne : walk ≠ []) :
    ∃ a ∈ S, ∃ b : Fin n, b ∉ S ∧ G.adj a b = true := by
  induction walk with
  | nil => exact False.elim (hne rfl)
  | cons x rest ih =>
    cases rest with
    | nil =>
      have hxS : x ∈ S := hs x rfl
      have hxn : x ∉ S := ht x rfl
      exact False.elim (hxn hxS)
    | cons y ys =>
      by_cases hy : y ∈ S
      · exact ih (fun s h => by simp at h; subst h; exact hy)
          (fun t h => ht t (by simpa using h)) hw.2 (by simp)
      · exact ⟨x, hs x rfl, y, hy, hw.1⟩

private theorem exists_notin_three (n : Nat) (hn : 4 ≤ n) (a b c : Fin n) :
    ∃ z : Fin n, z ≠ a ∧ z ≠ b ∧ z ≠ c := by
  have hflt : ((List.finRange n).filter (fun z => decide (z ≠ a) && decide (z ≠ b) && decide (z ≠ c))).length > 0 := by
    have hsum : sumNat (List.finRange n) (fun z => if (z = a ∨ z = b ∨ z = c) then 1 else 0) +
        ((List.finRange n).filter (fun z => decide (z ≠ a) && decide (z ≠ b) && decide (z ≠ c))).length = n := by
      have hm : ∀ f : Fin n → Nat, sumNat (List.finRange n) f =
          sumNat (List.finRange n) (fun z => if z = a ∨ z = b ∨ z = c then f z else 0) +
          sumNat (List.finRange n) (fun z => if (decide (z ≠ a) && decide (z ≠ b) && decide (z ≠ c)) = true then f z else 0) := by
        intro f; rw [← sumNat_add]; apply sumNat_congr; intro z _
        by_cases ha : z = a
        · subst ha; simp
        · by_cases hb : z = b
          · subst hb; simp [ha]
          · by_cases hc : z = c <;> simp [ha, hb, hc]
      have htot := hm (fun _ => 1)
      rw [sumNat_const_one, @List.length_finRange n, ← sumNat_filter_eq, sumNat_const_one] at htot
      omega
    have hle3 : sumNat (List.finRange n) (fun z => if (z = a ∨ z = b ∨ z = c) then 1 else 0) ≤ 3 := by
      have ha1 := sumNat_eq_indicator_one (List.finRange n) (List.nodup_finRange n) a (List.mem_finRange a)
      have hb1 := sumNat_eq_indicator_one (List.finRange n) (List.nodup_finRange n) b (List.mem_finRange b)
      have hc1 := sumNat_eq_indicator_one (List.finRange n) (List.nodup_finRange n) c (List.mem_finRange c)
      have hmono : sumNat (List.finRange n) (fun z => if (z = a ∨ z = b ∨ z = c) then 1 else 0) ≤
          sumNat (List.finRange n) (fun z => if z = a then 1 else 0) +
          sumNat (List.finRange n) (fun z => if z = b then 1 else 0) +
          sumNat (List.finRange n) (fun z => if z = c then 1 else 0) := by
        rw [← sumNat_add, ← sumNat_add]
        apply sumNat_mono; intro z _
        by_cases ha : z = a
        · subst ha; simp; omega
        · by_cases hb : z = b
          · subst hb; simp; omega
          · by_cases hc : z = c
            · subst hc; simp
            · simp [ha, hb, hc]
      omega
    omega
  cases hf : (List.finRange n).filter (fun z => decide (z ≠ a) && decide (z ≠ b) && decide (z ≠ c)) with
  | nil => rw [hf] at hflt; simp at hflt
  | cons z _ =>
    have hz : z ∈ (List.finRange n).filter (fun z => decide (z ≠ a) && decide (z ≠ b) && decide (z ≠ c)) := by
      rw [hf]; simp
    rw [List.mem_filter] at hz
    rcases (Bool.and_eq_true _ _).mp hz.2 with ⟨hab, hzc⟩
    rcases (Bool.and_eq_true _ _).mp hab with ⟨hza, hzb⟩
    exact ⟨z, of_decide_eq_true hza, of_decide_eq_true hzb, of_decide_eq_true hzc⟩

private theorem nodup_four {α : Type} {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ([a, b, c, d] : List α).Nodup := by
  simp [hab, hac, had, hbc, hbd, hcd]

private theorem exists_matching_two {n : Nat} (G : SimpleGraphFin n) (a b c d : Fin n)
    (hab : G.adj a b = true) (hcd : G.adj c d = true)
    (hdisj : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) :
    ∃ M : List (Fin n × Fin n), G.IsMatching M ∧ 2 ≤ M.length := by
  have hab_ne : a ≠ b := fun h => by subst h; rw [G.loopless] at hab; simp at hab
  have hcd_ne : c ≠ d := fun h => by subst h; rw [G.loopless] at hcd; simp at hcd
  let e1 := ordEdge a b
  let e2 := ordEdge c d
  have he1 : e1.1.val < e1.2.val ∧ G.adj e1.1 e1.2 = true := by
    dsimp [e1, ordEdge]
    by_cases h : a.val < b.val
    · simp [h, hab]
    · have : b.val < a.val := by have : a.val ≠ b.val := fun hv => hab_ne (Fin.ext hv); omega
      simp [h, this, G.symm b a, hab]
  have he2 : e2.1.val < e2.2.val ∧ G.adj e2.1 e2.2 = true := by
    dsimp [e2, ordEdge]
    by_cases h : c.val < d.val
    · simp [h, hcd]
    · have : d.val < c.val := by have : c.val ≠ d.val := fun hv => hcd_ne (Fin.ext hv); omega
      simp [h, this, G.symm d c, hcd]
  refine ⟨[e1, e2], ⟨fun e he => by
    rcases List.mem_cons.mp he with rfl | he'
    · exact he1
    · simp at he'; subst he'; exact he2, ?_⟩, by simp⟩
  rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  dsimp [e1, e2, ordEdge]
  by_cases h1 : a.val < b.val <;> by_cases h2 : c.val < d.val <;> simp only [h1, h2, ↓reduceIte]
  · exact nodup_four hab_ne hdisj.1 hdisj.2.1 hdisj.2.2.1 hdisj.2.2.2 hcd_ne
  · exact nodup_four hab_ne hdisj.2.1 hdisj.1 hdisj.2.2.2 hdisj.2.2.1 hcd_ne.symm
  · exact nodup_four hab_ne.symm hdisj.2.2.1 hdisj.2.2.2 hdisj.1 hdisj.2.1 hcd_ne
  · exact nodup_four hab_ne.symm hdisj.2.2.2 hdisj.2.2.1 hdisj.2.1 hdisj.1 hcd_ne.symm

theorem c4Free_minDeg_le_matching {n : Nat} (G : SimpleGraphFin n) (k : Nat)
    (hn : 4 ≤ n) (hConn : G.Connected) (hC4 : G.C4Free) (hM : G.MatchingNum k) :
    G.minDeg ≤ k := by
  have hmk : ∃ M : List (Fin n × Fin n), G.IsMatching M ∧ G.minDeg ≤ M.length := by
    let v0 : Fin n := ⟨0, by omega⟩
    have hv0_deg : G.minDeg ≤ G.deg v0 := G.minDeg_le_deg (by omega) v0
    by_cases hd0 : G.minDeg = 0
    · refine ⟨[], ⟨fun _ h => by simp at h, by simp⟩, by omega⟩
    · by_cases hd1 : G.minDeg = 1
      · have hpos : 0 < (List.finRange n).countP (G.adj v0) := by
          unfold deg at hv0_deg
          change G.minDeg ≤ (List.finRange n).countP (G.adj v0) at hv0_deg
          omega
        rcases exists_of_countP_pos (List.finRange n) (G.adj v0) hpos with ⟨u, _, hu⟩
        have hne : v0 ≠ u := fun h => by subst h; rw [G.loopless] at hu; simp at hu
        let e0 := ordEdge v0 u
        have he0 : e0.1.val < e0.2.val ∧ G.adj e0.1 e0.2 = true := by
          dsimp [e0, ordEdge]
          by_cases h : v0.val < u.val
          · simp [h, hu]
          · have : u.val < v0.val := by have : v0.val ≠ u.val := fun hv => hne (Fin.ext hv); omega
            simp [h, this, G.symm u v0, hu]
        refine ⟨[e0], ⟨fun e he => by simp at he; subst he; exact he0, ?_⟩, by simp [hd1]⟩
        rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nodup_cons, List.nodup_cons]
        exact ⟨fun h => by have := he0.1; simp at h; rw [h] at this; omega, by simp⟩
      · by_cases hd2 : G.minDeg = 2
        · have hge2 : 2 ≤ (List.finRange n).countP (G.adj v0) := by
            unfold deg at hv0_deg
            change G.minDeg ≤ (List.finRange n).countP (G.adj v0) at hv0_deg
            omega
          rcases two_of_countP_ge_two (List.finRange n) (List.nodup_finRange n) (G.adj v0) hge2 with
            ⟨u1, _, u2, _, hu12, hu1, hu2⟩
          have hv1 : v0 ≠ u1 := fun h => by subst h; rw [G.loopless] at hu1; simp at hu1
          have hv2 : v0 ≠ u2 := fun h => by subst h; rw [G.loopless] at hu2; simp at hu2
          by_cases ex1 : ∃ w1 : Fin n, G.adj u1 w1 = true ∧ w1 ≠ v0 ∧ w1 ≠ u2
          · rcases ex1 with ⟨w1, hw1, hnv, hnu⟩
            rcases exists_matching_two G u1 w1 v0 u2 hw1 hu2 ⟨hv1.symm, hu12, hnv, hnu⟩ with ⟨M, hIsM, hlen⟩
            exact ⟨M, hIsM, by omega⟩
          · by_cases ex2 : ∃ w2 : Fin n, G.adj u2 w2 = true ∧ w2 ≠ v0 ∧ w2 ≠ u1
            · rcases ex2 with ⟨w2, hw2, hnv, hnu⟩
              rcases exists_matching_two G u2 w2 v0 u1 hw2 hu1 ⟨hv2.symm, hu12.symm, hnv, hnu⟩ with ⟨M, hIsM, hlen⟩
              exact ⟨M, hIsM, by omega⟩
            · have h1_sub : ∀ w : Fin n, G.adj u1 w = true → w = v0 ∨ w = u2 := by
                intro w hw
                by_cases h1 : w = v0
                · exact Or.inl h1
                · by_cases h2 : w = u2
                  · exact Or.inr h2
                  · exact False.elim (ex1 ⟨w, hw, h1, h2⟩)
              have hu1_ge2 : 2 ≤ G.deg u1 := Nat.le_trans (by omega) (G.minDeg_le_deg (by omega) u1)
              have hadj12 : G.adj u1 u2 = true := by
                apply Classical.byContradiction
                intro hnf
                have hnf' : G.adj u1 u2 = false := Bool.eq_false_iff.mpr hnf
                have hv01 := sumNat_eq_indicator_one (List.finRange n) (List.nodup_finRange n) v0 (List.mem_finRange v0)
                have hle1 : G.deg u1 ≤ 1 := by
                  calc G.deg u1
                      = sumNat (List.finRange n) (fun w => if G.adj u1 w = true then 1 else 0) := by
                          unfold deg; rw [countP_eq_sumNat]
                    _ ≤ sumNat (List.finRange n) (fun w => if w = v0 then 1 else 0) := by
                          apply sumNat_mono; intro w _
                          cases hw : G.adj u1 w
                          · simp
                          · rcases h1_sub w hw with rfl | rfl
                            · simp
                            · rw [hw] at hnf'; simp at hnf'
                    _ = 1 := hv01
                omega
              rcases exists_notin_three n hn v0 u1 u2 with ⟨z, hzv, hzu1, hzu2⟩
              rcases hConn v0 z with ⟨walk, hne, hhead, hlast, hwalk⟩
              have hleave := walk_leaves_set G [v0, u1, u2] walk
                (fun s hs => by rw [hs] at hhead; injection hhead with hs'; subst hs'; simp)
                (fun t ht => by rw [ht] at hlast; injection hlast with ht'; subst ht'; simp [hzv, hzu1, hzu2])
                hwalk hne
              rcases hleave with ⟨a, haS, b, hbS, hab⟩
              have hb_ne : b ≠ v0 ∧ b ≠ u1 ∧ b ≠ u2 := by simpa [List.mem_cons] using hbS
              have ha_eq : a = v0 := by
                simp at haS
                rcases haS with rfl | rfl | rfl
                · rfl
                · rcases h1_sub b hab with rfl | rfl <;> exact False.elim (by simp_all)
                · by_cases hb_u1 : b = u1
                  · exact False.elim (hb_ne.2.1 hb_u1)
                  · exact False.elim (ex2 ⟨b, hab, hb_ne.1, hb_u1⟩)
              subst ha_eq
              rcases exists_matching_two G v0 b u1 u2 hab hadj12 ⟨hv1, hv2, hb_ne.2.1, hb_ne.2.2⟩ with ⟨M, hIsM, hlen⟩
              exact ⟨M, hIsM, by omega⟩
        · -- Case 3 <= G.minDeg: construct one unique external neighbor per u ∈ N0
          have hge3 : 3 ≤ G.minDeg := by omega
          let N0 := (List.finRange n).filter (G.adj v0)
          let Ext := (List.finRange n).filter (fun w => decide (w ≠ v0) && !G.adj v0 w)
          have hN0_nd : N0.Nodup := sg_nodup_filter _ (List.nodup_finRange n)
          have hN0_len : N0.length = G.deg v0 := by
            dsimp [N0, deg]
            rw [← sumNat_const_one, sumNat_filter_eq, countP_eq_sumNat]
          let partner : Fin n → Fin n := fun u => ((Ext.filter (G.adj u)).head?).getD v0
          have hN0_nbr_le1 : ∀ u ∈ N0, N0.countP (G.adj u) ≤ 1 := by
            intro u hu
            rw [List.mem_filter] at hu
            apply Classical.byContradiction
            intro hgt1
            have hge2 : 2 ≤ N0.countP (G.adj u) := by omega
            rcases two_of_countP_ge_two N0 hN0_nd (G.adj u) hge2 with ⟨w1, hw1m, w2, hw2m, hw12, hw1u, hw2u⟩
            rw [List.mem_filter] at hw1m hw2m
            have hvu : v0 ≠ u := fun h => by subst h; rw [G.loopless] at hu; simp at hu
            have hvw1 : v0 ≠ w1 := fun h => by subst h; rw [G.loopless] at hw1m; simp at hw1m
            have hvw2 : v0 ≠ w2 := fun h => by subst h; rw [G.loopless] at hw2m; simp at hw2m
            have huw1 : u ≠ w1 := fun h => by subst h; rw [G.loopless] at hw1u; simp at hw1u
            have huw2 : u ≠ w2 := fun h => by subst h; rw [G.loopless] at hw2u; simp at hw2u
            exact c4Free_not_cycle hC4 hvw1 hvu hvw2 huw1.symm hw12 huw2
              hw1m.2 (by rw [G.symm]; exact hw1u) hw2u (by rw [G.symm]; exact hw2m.2)
          have hpartner_spec : ∀ u ∈ N0, partner u ∈ Ext ∧ G.adj u (partner u) = true := by
            intro u hu
            have huN := hu
            rw [List.mem_filter] at hu
            have hdeg_split : G.deg u =
                (if G.adj u v0 then 1 else 0) + N0.countP (G.adj u) + Ext.countP (G.adj u) := by
              dsimp [deg, N0, Ext]
              rw [countP_eq_sumNat, countP_eq_sumNat, countP_eq_sumNat,
                  sumNat_filter_eq, sumNat_filter_eq]
              have hv01 := sumNat_eq_indicator_one (List.finRange n) (List.nodup_finRange n) v0 (List.mem_finRange v0)
              have hv_adj : (if G.adj u v0 then 1 else 0) = sumNat (List.finRange n) (fun w => if w = v0 then (if G.adj u w then 1 else 0) else 0) := by
                have hm := sumNat_const_mul (if G.adj u v0 then 1 else 0) (List.finRange n) (fun w => if w = v0 then 1 else 0)
                rw [hv01, Nat.mul_one] at hm
                rw [hm]; apply sumNat_congr; intro w _; by_cases hw : w = v0
                · subst hw; simp
                · simp [hw]
              rw [hv_adj, ← sumNat_add, ← sumNat_add]
              apply sumNat_congr; intro w _
              by_cases hwv : w = v0
              · subst hwv; simp [G.loopless]
              · cases G.adj v0 w <;> cases G.adj u w <;> simp [hwv]
            have huv0 : G.adj u v0 = true := G.symm v0 u ▸ hu.2
            have hdu : 3 ≤ G.deg u := Nat.le_trans hge3 (G.minDeg_le_deg (by omega) u)
            have hN1 := hN0_nbr_le1 u huN
            have hExt_pos : 0 < (Ext.filter (G.adj u)).length := by
              have hc : (Ext.filter (G.adj u)).length = Ext.countP (G.adj u) := by
                rw [← sumNat_const_one, sumNat_filter_eq, countP_eq_sumNat]
              simp [huv0] at hdeg_split
              omega
            cases hf : Ext.filter (G.adj u) with
            | nil => rw [hf] at hExt_pos; simp at hExt_pos
            | cons w _ =>
              have hpw : partner u = w := by dsimp [partner]; rw [hf]; rfl
              have hmem : w ∈ Ext.filter (G.adj u) := by rw [hf]; simp
              rw [List.mem_filter] at hmem
              simpa [hpw] using hmem
          have hpartner_inj : ∀ u1 ∈ N0, ∀ u2 ∈ N0, partner u1 = partner u2 → u1 = u2 := by
            intro u1 hu1 u2 hu2 heq
            apply Classical.byContradiction
            intro hne
            have hs1 := hpartner_spec u1 hu1
            have hs2 := hpartner_spec u2 hu2
            rw [← heq] at hs2
            let w := partner u1
            have hwE : w ∈ Ext := hs1.1
            rw [List.mem_filter] at hwE hu1 hu2
            rcases (Bool.and_eq_true _ _).mp hwE.2 with ⟨hwv', hvnw'⟩
            have hwv : w ≠ v0 := of_decide_eq_true hwv'
            have hvnw : G.adj v0 w = false := by simpa using hvnw'
            have hwu1 : w ≠ u1 := fun h => by rw [h, hu1.2] at hvnw; simp at hvnw
            have hwu2 : w ≠ u2 := fun h => by rw [h, hu2.2] at hvnw; simp at hvnw
            have hvu1 : v0 ≠ u1 := fun h => by subst h; rw [G.loopless] at hu1; simp at hu1
            have hvu2 : v0 ≠ u2 := fun h => by subst h; rw [G.loopless] at hu2; simp at hu2
            exact c4Free_not_cycle hC4 hvu1 hwv.symm hvu2 hwu1.symm hne hwu2
              hu1.2 hs1.2 (by rw [G.symm]; exact hs2.2) (by rw [G.symm]; exact hu2.2)
          have hdisj : ∀ x ∈ N0, partner x ∉ N0 := by
            intro x hx hm
            have hsp := (hpartner_spec x hx).1
            rw [List.mem_filter] at hsp hm
            rcases (Bool.and_eq_true _ _).mp hsp.2 with ⟨_, hnf⟩
            rw [hm.2] at hnf
            simp at hnf
          have hmap_nd : ∀ S : List (Fin n), S.Nodup → (∀ u ∈ S, u ∈ N0) →
              ((S.map (fun u => ordEdge u (partner u))).flatMap (fun e => [e.1, e.2])).Nodup := by
            intro S hSnd hSsub
            induction S with
            | nil => simp
            | cons u rest ih =>
              rw [List.nodup_cons] at hSnd
              have huN : u ∈ N0 := hSsub u (by simp)
              have hu_ne : u ≠ partner u := fun h => hdisj u huN (h ▸ huN)
              have hpair_mem : ∀ z, z ∈ ((rest.map (fun r => ordEdge r (partner r))).flatMap (fun e => [e.1, e.2])) →
                  ∃ r ∈ rest, z = r ∨ z = partner r := by
                intro z hz
                rw [List.mem_flatMap] at hz
                rcases hz with ⟨e, he, hze⟩
                rw [List.mem_map] at he
                rcases he with ⟨r, hr, rfl⟩
                exact ⟨r, hr, (mem_ordEdge_iff r (partner r) z).mp hze⟩
              have hu_notin : u ∉ (rest.map (fun r => ordEdge r (partner r))).flatMap (fun e => [e.1, e.2]) := by
                intro hm
                rcases hpair_mem u hm with ⟨r, hr, rfl | hEq⟩
                · exact hSnd.1 hr
                · exact hdisj r (hSsub r (List.mem_cons_of_mem u hr)) (hEq ▸ huN)
              have hw_notin : partner u ∉ (rest.map (fun r => ordEdge r (partner r))).flatMap (fun e => [e.1, e.2]) := by
                intro hm
                rcases hpair_mem (partner u) hm with ⟨r, hr, hEq | hEq⟩
                · exact hdisj u huN (hEq ▸ hSsub r (List.mem_cons_of_mem u hr))
                · have hr_eq := hpartner_inj u huN r (hSsub r (List.mem_cons_of_mem u hr)) hEq
                  subst hr_eq; exact hSnd.1 hr
              rw [List.map_cons, List.flatMap_cons]
              have ihr := ih hSnd.2 (fun r hr => hSsub r (List.mem_cons_of_mem u hr))
              have heord : [(ordEdge u (partner u)).1, (ordEdge u (partner u)).2] ++
                  (rest.map (fun r => ordEdge r (partner r))).flatMap (fun e => [e.1, e.2]) =
                  (ordEdge u (partner u)).1 :: (ordEdge u (partner u)).2 ::
                  (rest.map (fun r => ordEdge r (partner r))).flatMap (fun e => [e.1, e.2]) := by simp
              rw [heord]
              by_cases hlt : u.val < (partner u).val
              · simp only [ordEdge, hlt, ↓reduceIte, List.nodup_cons]
                refine ⟨fun hm => ?_, hw_notin, ihr⟩
                rcases List.mem_cons.mp hm with heq | hm'
                · exact hu_ne heq
                · exact hu_notin hm'
              · simp only [ordEdge, hlt, ↓reduceIte, List.nodup_cons]
                refine ⟨fun hm => ?_, hu_notin, ihr⟩
                rcases List.mem_cons.mp hm with heq | hm'
                · exact hu_ne heq.symm
                · exact hw_notin hm'
          let M := N0.map (fun u => ordEdge u (partner u))
          refine ⟨M, ⟨?_, hmap_nd N0 hN0_nd (fun _ h => h)⟩, ?_⟩
          · intro e he
            dsimp [M] at he
            rw [List.mem_map] at he
            rcases he with ⟨u, hu, rfl⟩
            have hu_ne : u ≠ partner u := fun h => hdisj u hu (h ▸ hu)
            have hw := hpartner_spec u hu
            dsimp [ordEdge]
            by_cases hlt : u.val < (partner u).val
            · simp [hlt, hw.2]
            · have hlt' : (partner u).val < u.val := by
                have : (partner u).val ≠ u.val := fun h => hu_ne (Fin.ext h.symm)
                omega
              simp [hlt, hlt', G.symm u (partner u) ▸ hw.2]
          · dsimp [M]; rw [List.length_map, hN0_len]; exact hv0_deg
  rcases hmk with ⟨M, hIsM, hlen⟩
  exact Nat.le_trans hlen (hM.2 M hIsM)

end SimpleGraphFin

-- ============================================================================
-- Theorem 8 (Round 3): Integer Restricted Sumset Bound & 3-AP-Free Identity
-- ============================================================================

private def isDoubleIn (A : Nat → Bool) (N s : Nat) : Bool :=
  decide (s % 2 = 0 ∧ s / 2 < N) && A (s / 2)

private theorem countP_range_isDoubleIn (A : Nat → Bool) (N : Nat) :
    (List.range (2 * N)).countP (isDoubleIn A N) = cardPrefix A N := by
  induction N with
  | zero =>
    simp [cardPrefix, sumNat]
  | succ N ih =>
    have hr : 2 * (N + 1) = (2 * N + 1) + 1 := by omega
    rw [hr, List.range_succ, List.countP_append, List.range_succ, List.countP_append]
    have hprefix : (List.range (2 * N)).countP (isDoubleIn A (N + 1)) =
        (List.range (2 * N)).countP (isDoubleIn A N) := by
      rw [countP_eq_sumNat, countP_eq_sumNat]
      apply sumNat_congr
      intro s hs
      have hlt : s < 2 * N := List.mem_range.mp hs
      have hdiv : s / 2 < N := by omega
      have hdiv1 : s / 2 < N + 1 := by omega
      unfold isDoubleIn
      simp [hdiv, hdiv1]
    have heven : isDoubleIn A (N + 1) (2 * N) = A N := by
      unfold isDoubleIn
      have hm : (2 * N) % 2 = 0 := by omega
      have hd : (2 * N) / 2 = N := by omega
      have hlt : N < N + 1 := by omega
      simp [hm, hd, hlt]
    have hodd : isDoubleIn A (N + 1) (2 * N + 1) = false := by
      unfold isDoubleIn
      simp
    have hcp : cardPrefix A (N + 1) = cardPrefix A N + (if A N then 1 else 0) := by
      unfold cardPrefix
      rw [List.range_succ, sumNat_append]
      simp [sumNat]
    rw [hprefix, ih, hcp]
    simp only [List.countP_cons, List.countP_nil, heven, hodd]
    cases A N <;> simp <;> omega

private theorem mem_sumset_pred_cases (A : Nat → Bool) (N s : Nat)
    (hs : (List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a + b = s))) = true) :
    (List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a < b) && decide (a + b = s))) = true ∨
      isDoubleIn A N s = true := by
  rw [List.any_eq_true] at hs
  rcases hs with ⟨a, ha_mem, ha_any⟩
  rw [List.any_eq_true] at ha_any
  rcases ha_any with ⟨b, hb_mem, hab⟩
  have haN : a < N := List.mem_range.mp ha_mem
  have hbN : b < N := List.mem_range.mp hb_mem
  rcases (Bool.and_eq_true _ _).mp hab with ⟨hab_bool, hsum⟩
  rcases (Bool.and_eq_true _ _).mp hab_bool with ⟨hAa, hAb⟩
  have heq_sum : a + b = s := decide_eq_true_iff.mp hsum
  by_cases hlt : a < b
  · left
    rw [List.any_eq_true]
    refine ⟨a, ha_mem, ?_⟩
    rw [List.any_eq_true]
    refine ⟨b, hb_mem, ?_⟩
    simp [hAa, hAb, hlt, heq_sum]
  · by_cases heq : a = b
    · right
      subst heq
      unfold isDoubleIn
      have hm : s % 2 = 0 := by omega
      have hd : s / 2 = a := by omega
      simp [hm, hd, haN, hAa]
    · left
      have hgt : b < a := by omega
      rw [List.any_eq_true]
      refine ⟨b, hb_mem, ?_⟩
      rw [List.any_eq_true]
      refine ⟨a, ha_mem, ?_⟩
      have hsum' : b + a = s := by omega
      simp [hAa, hAb, hgt, hsum']

private theorem restSum_or_double_implies_sumset (A : Nat → Bool) (N s : Nat) :
    ((List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a < b) && decide (a + b = s))) = true →
      (List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a + b = s))) = true) ∧
    (isDoubleIn A N s = true →
      (List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a + b = s))) = true) := by
  constructor
  · intro hr
    rw [List.any_eq_true] at hr
    rcases hr with ⟨a, ha_mem, ha_any⟩
    rw [List.any_eq_true] at ha_any
    rcases ha_any with ⟨b, hb_mem, hab⟩
    rcases (Bool.and_eq_true _ _).mp hab with ⟨hab1, hsum⟩
    rcases (Bool.and_eq_true _ _).mp hab1 with ⟨hab0, _⟩
    rcases (Bool.and_eq_true _ _).mp hab0 with ⟨hAa, hAb⟩
    have heq : a + b = s := decide_eq_true_iff.mp hsum
    rw [List.any_eq_true]
    refine ⟨a, ha_mem, ?_⟩
    rw [List.any_eq_true]
    refine ⟨b, hb_mem, ?_⟩
    simp [hAa, hAb, heq]
  · intro hd
    unfold isDoubleIn at hd
    rcases (Bool.and_eq_true _ _).mp hd with ⟨hdec, hAc⟩
    have hdiv_lt : s % 2 = 0 ∧ s / 2 < N := decide_eq_true_iff.mp hdec
    have hc_mem : s / 2 ∈ List.range N := List.mem_range.mpr hdiv_lt.2
    have hsum : s / 2 + s / 2 = s := by omega
    rw [List.any_eq_true]
    refine ⟨s / 2, hc_mem, ?_⟩
    rw [List.any_eq_true]
    refine ⟨s / 2, hc_mem, ?_⟩
    simp [hAc, hsum]

theorem intSumsetCard_le_intRestSumCard_add_card (A : Nat → Bool) (N : Nat) :
    intSumsetCard A N ≤ intRestSumCard A N + cardPrefix A N := by
  unfold intSumsetCard intRestSumCard
  rw [← countP_range_isDoubleIn A N]
  rw [countP_eq_sumNat, countP_eq_sumNat, countP_eq_sumNat, ← sumNat_add]
  apply sumNat_mono
  intro s _
  by_cases hs : (List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a + b = s))) = true
  · rcases mem_sumset_pred_cases A N s hs with hrest | hdbl
    · simp [hs, hrest]
    · simp [hs, hdbl]
  · have hsf : (List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a + b = s))) = false := by
      cases hval : (List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a + b = s)))
      · rfl
      · exact absurd hval hs
    simp [hsf]

theorem ap3Free_intSumsetCard_eq_intRestSumCard_add_card (A : Nat → Bool) (N : Nat)
    (hap : IsAP3FreePrefix A N) :
    intSumsetCard A N = intRestSumCard A N + cardPrefix A N := by
  unfold intSumsetCard intRestSumCard
  rw [← countP_range_isDoubleIn A N]
  rw [countP_eq_sumNat, countP_eq_sumNat, countP_eq_sumNat, ← sumNat_add]
  apply sumNat_congr
  intro s _
  have himpl := restSum_or_double_implies_sumset A N s
  by_cases hr : (List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a < b) && decide (a + b = s))) = true
  · have hs : (List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a + b = s))) = true :=
      himpl.1 hr
    have hd_false : isDoubleIn A N s = false := by
      cases hd : isDoubleIn A N s
      · rfl
      · exfalso
        rw [List.any_eq_true] at hr
        rcases hr with ⟨a, ha_mem, ha_any⟩
        rw [List.any_eq_true] at ha_any
        rcases ha_any with ⟨b, hb_mem, hab⟩
        rcases (Bool.and_eq_true _ _).mp hab with ⟨hab1, hsum⟩
        rcases (Bool.and_eq_true _ _).mp hab1 with ⟨hab0, hlt⟩
        rcases (Bool.and_eq_true _ _).mp hab0 with ⟨hAa, hAb⟩
        have haN : a < N := List.mem_range.mp ha_mem
        have hbN : b < N := List.mem_range.mp hb_mem
        have hab_lt : a < b := decide_eq_true_iff.mp hlt
        have heq_sum : a + b = s := decide_eq_true_iff.mp hsum
        unfold isDoubleIn at hd
        rcases (Bool.and_eq_true _ _).mp hd with ⟨hdec, hAc⟩
        have hcd : s % 2 = 0 ∧ s / 2 < N := decide_eq_true_iff.mp hdec
        have hap_bad : a + b = 2 * (s / 2) := by omega
        exact hap a b (s / 2) haN hbN hcd.2 hAa hAb hAc hab_lt hap_bad
    simp [hs, hr, hd_false]
  · have hrf : (List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a < b) && decide (a + b = s))) = false := by
      cases hval : (List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a < b) && decide (a + b = s)))
      · rfl
      · exact absurd hval hr
    by_cases hd : isDoubleIn A N s = true
    · have hs := himpl.2 hd
      simp [hs, hrf, hd]
    · have hdf : isDoubleIn A N s = false := by
        cases hval : isDoubleIn A N s
        · rfl
        · exact absurd hval hd
      have hsf : (List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a + b = s))) = false := by
        cases hval : (List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a + b = s)))
        · rfl
        · rcases mem_sumset_pred_cases A N s hval with h1 | h2
          · exact absurd h1 hr
          · exact absurd h2 hd
      simp [hsf, hrf, hdf]

-- ============================================================================
-- Theorem 9 (Round 3): West Stack-Sorting Inversions <= pat_231
-- ============================================================================

private theorem pairwise_append_rel {α : Type} {R : α → α → Prop} :
    ∀ {xs ys : List α}, (xs ++ ys).Pairwise R → ∀ a ∈ xs, ∀ b ∈ ys, R a b := by
  intro xs ys hpw a ha b hb
  induction xs with
  | nil => simp at ha
  | cons x rest ih =>
    simp only [List.cons_append] at hpw
    cases hpw with
    | cons hx hrest =>
      rcases List.mem_cons.mp ha with rfl | hare
      · exact hx b (List.mem_append_right rest hb)
      · exact ih hrest hare

private theorem pairwise_mono_sublist {α : Type} {R : α → α → Prop} :
    ∀ {xs ys : List α}, ys.Pairwise R → xs.Sublist ys → xs.Pairwise R := by
  intro xs ys hpw hsub
  induction hsub with
  | slnil => exact .nil
  | cons _ _ ih =>
    cases hpw with
    | cons _ hrest => exact ih hrest
  | cons_cons a hsub' ih =>
    cases hpw with
    | cons ha hrest =>
      exact .cons (fun b hb => ha b (hsub'.subset hb)) (ih hrest)

private theorem westStep_spec (stk : List Nat) (x : Nat) (hstk : stk.Pairwise (· ≤ ·)) :
    ∃ stk_rem,
      stk = (westStep stk x).1 ++ stk_rem ∧
      (westStep stk x).2 = x :: stk_rem ∧
      (∀ s ∈ (westStep stk x).1, s < x) ∧
      (∀ u ∈ stk_rem, x ≤ u) ∧
      (westStep stk x).1.Pairwise (· ≤ ·) ∧
      (westStep stk x).2.Pairwise (· ≤ ·) := by
  induction stk with
  | nil =>
    refine ⟨[], rfl, rfl, fun _ h => by simp [westStep] at h, fun _ h => by simp at h, ?_, ?_⟩
    · simp [westStep]
    · simp only [westStep]
      exact .cons (fun _ h => by simp at h) .nil
  | cons top rest ih =>
    cases hstk with
    | cons htop hrest =>
      by_cases hlt : top < x
      · rcases ih hrest with ⟨stk_rem, hsplit, hstk2, hpop, hrem, hpw_pop, hpw_stk2⟩
        have hstep : westStep (top :: rest) x = (top :: (westStep rest x).1, (westStep rest x).2) := by
          simp [westStep, hlt]
        refine ⟨stk_rem, ?_, ?_, ?_, hrem, ?_, ?_⟩
        · rw [hstep]; simp only [List.cons_append]; rw [← hsplit]
        · rw [hstep]; exact hstk2
        · intro s hs
          rw [hstep] at hs
          rcases List.mem_cons.mp hs with rfl | hs'
          · exact hlt
          · exact hpop s hs'
        · rw [hstep]
          refine .cons (fun z hz => htop z ?_) hpw_pop
          rw [hsplit]
          exact List.mem_append_left stk_rem hz
        · rw [hstep]; exact hpw_stk2
      · have hle : x ≤ top := by omega
        have hstep : westStep (top :: rest) x = ([], x :: top :: rest) := by
          simp [westStep, hlt]
        refine ⟨top :: rest, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hstep]; rfl
        · rw [hstep]
        · intro _ h; rw [hstep] at h; simp at h
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu'
          · exact hle
          · exact Nat.le_trans hle (htop u hu')
        · rw [hstep]; exact .nil
        · rw [hstep]
          refine .cons (fun u hu => ?_) (.cons htop hrest)
          rcases List.mem_cons.mp hu with rfl | hu'
          · exact hle
          · exact Nat.le_trans hle (htop u hu')

private theorem westSortAux_countP (P : Nat → Bool) (xs stk : List Nat) :
    (westSortAux xs stk).countP P = stk.countP P + xs.countP P := by
  induction xs generalizing stk with
  | nil => simp [westSortAux]
  | cons x xs ih =>
    unfold westSortAux
    have hstep_sum : ∀ s : List Nat, (westStep s x).1.countP P + (westStep s x).2.countP P =
        s.countP P + (if P x then 1 else 0) := by
      intro s
      induction s with
      | nil =>
        simp only [westStep, List.countP_nil, List.countP_cons]
        cases hpx : P x <;> simp <;> omega
      | cons t ts ihs =>
        by_cases hlt : t < x
        · have hs : westStep (t :: ts) x = (t :: (westStep ts x).1, (westStep ts x).2) := by
            simp [westStep, hlt]
          rw [hs, List.countP_cons, List.countP_cons]
          have iht := ihs
          cases hpt : P t <;> simp <;> omega
        · have hs : westStep (t :: ts) x = ([], x :: t :: ts) := by
            simp [westStep, hlt]
          rw [hs, List.countP_nil, List.countP_cons, List.countP_cons]
          cases hpx : P x <;> cases hpt : P t <;> simp <;> omega
    rw [List.countP_append, ih, List.countP_cons, ← Nat.add_assoc, hstep_sum stk]
    omega

private theorem countP_eq_zero_of_forall {α : Type} (xs : List α) (P : α → Bool)
    (h : ∀ x ∈ xs, P x = false) : xs.countP P = 0 := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    rw [List.countP_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    rfl

private theorem listInvCnt_eq_zero_of_pairwise {xs : List Nat} (hpw : xs.Pairwise (· ≤ ·)) :
    listInvCnt xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases hpw with
    | cons hx hrest =>
      unfold listInvCnt
      have h0 : rest.countP (fun b => decide (b < x)) = 0 := by
        apply countP_eq_zero_of_forall
        intro b hb
        have hle := hx b hb
        exact decide_eq_false (by omega)
      rw [h0, ih hrest]

private theorem listInvCnt_append (ys zs : List Nat) :
    listInvCnt (ys ++ zs) =
      listInvCnt ys + sumNat ys (fun a => zs.countP (fun b => decide (b < a))) + listInvCnt zs := by
  induction ys with
  | nil => simp [listInvCnt, sumNat]
  | cons a yr ih =>
    simp only [List.cons_append, listInvCnt, sumNat, List.countP_append, ih]
    omega

private theorem westSortAux_inv_le : ∀ (xs stk : List Nat), stk.Pairwise (· ≤ ·) →
    listInvCnt (westSortAux xs stk) ≤ pat231List xs + sumNat stk (fun s => pairs31 xs s)
  | [], stk, hstk => by
    have hz := listInvCnt_eq_zero_of_pairwise hstk
    simp [westSortAux, pat231List, hz]
  | x :: xs, stk, hstk => by
    unfold westSortAux
    rcases westStep_spec stk x hstk with ⟨stk_rem, hsplit, hstk2, hpop_lt, hrem_ge, hpop_pw, hstk2_pw⟩
    change listInvCnt ((westStep stk x).1 ++ westSortAux xs (westStep stk x).2) ≤
      pat231List (x :: xs) + sumNat stk (fun s => pairs31 (x :: xs) s)
    have hih := westSortAux_inv_le xs (westStep stk x).2 hstk2_pw
    have hstk'_sum : sumNat (westStep stk x).2 (fun s => pairs31 xs s) =
        pairs31 xs x + sumNat stk_rem (fun u => pairs31 xs u) := by
      rw [hstk2]
      simp [sumNat]
    have hcross : ∀ s ∈ (westStep stk x).1,
        (westSortAux xs (westStep stk x).2).countP (fun c => decide (c < s)) =
        xs.countP (fun c => decide (c < s)) := by
      intro s hs
      rw [westSortAux_countP, hstk2, List.countP_cons]
      have hs_x : decide (x < s) = false := decide_eq_false (by have := hpop_lt s hs; omega)
      have hstk_pw2 : ((westStep stk x).1 ++ stk_rem).Pairwise (· ≤ ·) := by rwa [← hsplit]
      have hrem_zero : stk_rem.countP (fun c => decide (c < s)) = 0 := by
        apply countP_eq_zero_of_forall
        intro u hu
        have hsu := pairwise_append_rel hstk_pw2 s hs u hu
        exact decide_eq_false (by omega)
      rw [hrem_zero, hs_x]
      simp
    have hpop_sum : sumNat (westStep stk x).1 (fun s => (westSortAux xs (westStep stk x).2).countP (fun c => decide (c < s))) =
        sumNat (westStep stk x).1 (fun s => xs.countP (fun c => decide (c < s))) :=
      sumNat_congr (westStep stk x).1 _ _ hcross
    have hrhs_split : sumNat stk (fun s => pairs31 (x :: xs) s) =
        sumNat (westStep stk x).1 (fun s => pairs31 (x :: xs) s) +
        sumNat stk_rem (fun u => pairs31 (x :: xs) u) := by
      have hs1 := congrArg (fun l => sumNat l (fun s => pairs31 (x :: xs) s)) hsplit
      exact hs1.trans (sumNat_append _ _ _)
    have hrhs_pop : sumNat (westStep stk x).1 (fun s => pairs31 (x :: xs) s) =
        sumNat (westStep stk x).1 (fun s => xs.countP (fun c => decide (c < s)) + pairs31 xs s) := by
      apply sumNat_congr
      intro s hs
      have hlt := hpop_lt s hs
      simp [pairs31, hlt]
    have hrhs_rem : sumNat stk_rem (fun u => pairs31 (x :: xs) u) =
        sumNat stk_rem (fun u => pairs31 xs u) := by
      apply sumNat_congr
      intro u hu
      have hle := hrem_ge u hu
      have hnlt : ¬ (u < x) := by omega
      simp [pairs31, hnlt]
    have hpop_zero : listInvCnt (westStep stk x).1 = 0 := listInvCnt_eq_zero_of_pairwise hpop_pw
    have hpop_split2 : sumNat (westStep stk x).1 (fun s => xs.countP (fun c => decide (c < s)) + pairs31 xs s) =
        sumNat (westStep stk x).1 (fun s => xs.countP (fun c => decide (c < s))) +
        sumNat (westStep stk x).1 (fun s => pairs31 xs s) :=
      sumNat_add (westStep stk x).1 _ _
    have hpat : pat231List (x :: xs) = pairs31 xs x + pat231List xs := by rfl
    rw [listInvCnt_append (westStep stk x).1 (westSortAux xs (westStep stk x).2), hpop_zero, hpop_sum]
    rw [hrhs_split, hrhs_pop, hrhs_rem, hpop_split2, hpat]
    rw [hstk'_sum] at hih
    clear hcross hpop_sum hrhs_split hrhs_pop hrhs_rem hpop_zero hpop_split2 hpat hstk'_sum
    omega

theorem westSortList_inv_le_pat231 (xs : List Nat) :
    listInvCnt (westSortList xs) ≤ pat231List xs := by
  have h := westSortAux_inv_le xs [] .nil
  simpa [westSortList, sumNat] using h

theorem westSortList_inv_eq_zero_of_pat231_zero (xs : List Nat) (h0 : pat231List xs = 0) :
    listInvCnt (westSortList xs) = 0 := by
  have h := westSortList_inv_le_pat231 xs
  omega

theorem PermFin.stackInv_le_pat231 {n : Nat} (p : PermFin n) :
    p.stackInv ≤ p.pat231 :=
  westSortList_inv_le_pat231 p.toList

-- ============================================================================
-- Theorem 10 (Round 4): Pop-Stack Sorting Inversions + Descents <= Inversions
-- ============================================================================

private def concatRuns : List (List Nat) → List Nat
  | [] => []
  | r :: rs => r ++ concatRuns rs

private theorem concatRuns_popRuns (xs : List Nat) :
    concatRuns (popRuns xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases hpr : popRuns rest with
    | nil =>
      rw [hpr, concatRuns] at ih
      subst ih
      simp [popRuns, concatRuns]
    | cons r0 rs =>
      cases r0 with
      | nil =>
        simp only [popRuns, hpr, concatRuns]
        simpa [hpr, concatRuns] using ih
      | cons y ys =>
        simp only [popRuns, hpr]
        by_cases hlt : y < x
        · simp only [hlt, ↓reduceIte, concatRuns, List.cons_append]
          congr 1
          simpa [hpr, concatRuns] using ih
        · simp only [hlt, ↓reduceIte, concatRuns, List.singleton_append]
          congr 1
          simpa [hpr, concatRuns] using ih

private theorem popRuns_nonempty_and_pairwise (xs : List Nat) :
    ∀ r ∈ popRuns xs, r ≠ [] ∧ r.Pairwise (· > ·) := by
  induction xs with
  | nil =>
    intro r hr
    simp [popRuns] at hr
  | cons x rest ih =>
    cases hpr : popRuns rest with
    | nil =>
      intro r hr
      simp only [popRuns, hpr, List.mem_singleton] at hr
      subst hr
      exact ⟨by simp, by simp⟩
    | cons r0 rs =>
      have hr0 := ih r0 (by rw [hpr]; simp)
      cases r0 with
      | nil => exact absurd rfl hr0.1
      | cons y ys =>
        simp only [popRuns, hpr]
        by_cases hlt : y < x
        · simp only [hlt, ↓reduceIte, List.mem_cons]
          intro r hr
          rcases hr with rfl | hmem
          · refine ⟨by simp, List.pairwise_cons.mpr ⟨?_, hr0.2⟩⟩
            intro z hz
            rcases List.mem_cons.mp hz with rfl | hzs
            · exact hlt
            · have hyz := (List.pairwise_cons.mp hr0.2).1 z hzs
              omega
          · exact ih r (by rw [hpr]; exact List.mem_cons_of_mem _ hmem)
        · simp only [hlt, ↓reduceIte, List.mem_cons]
          intro r hr
          rcases hr with rfl | hmem
          · exact ⟨by simp, by simp⟩
          · exact ih r (by rw [hpr]; exact List.mem_cons.mpr hmem)

private theorem sumNat_popRuns_pred_eq_des :
    ∀ xs : List Nat, sumNat (popRuns xs) (fun r => r.length - 1) = desList xs
  | [] => by simp [popRuns, sumNat, desList]
  | [x] => by simp [popRuns, sumNat, desList]
  | x :: y :: ys => by
    have ih := sumNat_popRuns_pred_eq_des (y :: ys)
    have hc := concatRuns_popRuns (y :: ys)
    cases hpr : popRuns (y :: ys) with
    | nil =>
      rw [hpr, concatRuns] at hc
      cases hc
    | cons r0 rs =>
      have hr0ne := (popRuns_nonempty_and_pairwise (y :: ys) r0 (by rw [hpr]; simp)).1
      cases r0 with
      | nil => exact absurd rfl hr0ne
      | cons h t =>
        rw [hpr] at hc
        simp only [concatRuns, List.cons_append] at hc
        injection hc with hy _
        subst h
        rw [hpr] at ih
        change sumNat (match popRuns (y :: ys) with
          | [] => [[x]]
          | (u :: us) :: runs => if u < x then (x :: u :: us) :: runs else [x] :: (u :: us) :: runs
          | [] :: runs => [x] :: runs) (fun r => r.length - 1) = desList (x :: y :: ys)
        rw [hpr]
        have hdx : desList (x :: y :: ys) = (if x > y then 1 else 0) + desList (y :: ys) := rfl
        by_cases hlt : y < x
        · simp only [hlt, ↓reduceIte, sumNat, List.length_cons, Nat.add_sub_cancel] at ih ⊢
          have hxgt : x > y := hlt
          have h1 : (if x > y then 1 else 0) = 1 := by simp [hxgt]
          rw [hdx, h1]
          omega
        · have hnotgt : ¬ (x > y) := by omega
          have h0 : (if x > y then 1 else 0) = 0 := by simp [hnotgt]
          rw [hdx, h0]
          simp only [hlt, ↓reduceIte, sumNat, List.length_singleton, Nat.sub_self, Nat.zero_add]
          simpa [sumNat] using ih

private theorem countP_reverse (P : Nat → Bool) (r : List Nat) :
    r.reverse.countP P = r.countP P := by
  induction r with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons, List.countP_append, List.countP_cons, List.countP_nil, ih]
    cases P x <;> simp <;> omega

private theorem sumNat_reverse (r : List Nat) (f : Nat → Nat) :
    sumNat r.reverse f = sumNat r f := by
  induction r with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons, sumNat_append, sumNat, ih]
    omega

private theorem flatMap_reverse_countP (P : Nat → Bool) (L : List (List Nat)) :
    (L.flatMap List.reverse).countP P = (concatRuns L).countP P := by
  induction L with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.flatMap_cons, concatRuns, List.countP_append, countP_reverse, ih]

private theorem pairwise_append_singleton {α : Type} {R : α → α → Prop}
    {xs : List α} {a : α} (hpw : xs.Pairwise R) (ha : ∀ z ∈ xs, R z a) :
    (xs ++ [a]).Pairwise R := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    cases hpw with
    | cons hx hrest =>
      simp only [List.cons_append, List.pairwise_cons]
      refine ⟨fun z hz => ?_, ih hrest (fun z hz => ha z (by simp [hz]))⟩
      rcases List.mem_append.mp hz with hzr | hza
      · exact hx z hzr
      · simp at hza
        subst hza
        exact ha x (by simp)

private theorem reverse_pairwise_le_of_gt {r : List Nat} (hr : r.Pairwise (· > ·)) :
    r.reverse.Pairwise (· ≤ ·) := by
  induction r with
  | nil => simp
  | cons x rest ih =>
    cases hr with
    | cons hx hrest =>
      simp only [List.reverse_cons]
      refine pairwise_append_singleton (ih hrest) (fun z hz => ?_)
      have hz' : z ∈ rest := List.mem_reverse.mp hz
      have hgt := hx z hz'
      omega

private theorem pairwise_gt_pred_le_inv :
    ∀ r : List Nat, r.Pairwise (· > ·) → r.length - 1 ≤ listInvCnt r
  | [], _ => by simp [listInvCnt]
  | [_], _ => by simp [listInvCnt]
  | a :: b :: rest, hpw => by
    cases hpw with
    | cons hab hrest =>
      have h1 : b < a := hab b (by simp)
      have hge1 : 1 ≤ (b :: rest).countP (fun z => decide (z < a)) := by
        simp only [List.countP_cons, decide_eq_true h1, ↓reduceIte]
        omega
      have ih := pairwise_gt_pred_le_inv (b :: rest) hrest
      unfold listInvCnt
      simp only [List.length_cons] at ih ⊢
      omega

private theorem runs_inv_add_pred_le (L : List (List Nat)) (hL : ∀ r ∈ L, r.Pairwise (· > ·)) :
    listInvCnt (L.flatMap List.reverse) + sumNat L (fun r => r.length - 1) ≤
    listInvCnt (concatRuns L) := by
  induction L with
  | nil => simp [concatRuns, sumNat, listInvCnt]
  | cons r rs ih =>
    have hr : r.Pairwise (· > ·) := hL r (by simp)
    have hrs := ih (fun s hs => hL s (by simp [hs]))
    have hr0 : listInvCnt r.reverse = 0 := listInvCnt_eq_zero_of_pairwise (reverse_pairwise_le_of_gt hr)
    have hpred : r.length - 1 ≤ listInvCnt r := pairwise_gt_pred_le_inv r hr
    have hcross :
        sumNat r.reverse (fun a => (rs.flatMap List.reverse).countP (fun b => decide (b < a))) =
        sumNat r (fun a => (concatRuns rs).countP (fun b => decide (b < a))) := by
      rw [sumNat_reverse]
      apply sumNat_congr
      intro a _
      exact flatMap_reverse_countP (fun b => decide (b < a)) rs
    simp only [List.flatMap_cons, concatRuns, sumNat]
    rw [listInvCnt_append r.reverse (rs.flatMap List.reverse)]
    rw [listInvCnt_append r (concatRuns rs)]
    rw [hr0, hcross]
    omega

theorem popSortList_inv_add_des_le_inv (xs : List Nat) :
    listInvCnt (popSortList xs) + desList xs ≤ listInvCnt xs := by
  have h1 := runs_inv_add_pred_le (popRuns xs) (fun r hr => (popRuns_nonempty_and_pairwise xs r hr).2)
  rw [concatRuns_popRuns xs, sumNat_popRuns_pred_eq_des xs] at h1
  simpa [popSortList] using h1

private theorem sumNat_range_succ_front (m : Nat) (f : Nat → Nat) :
    sumNat (List.range (m + 1)) f = f 0 + sumNat (List.range m) (fun t => f (t + 1)) := by
  rw [List.range_succ_eq_map, sumNat, sumNat_map]

private theorem listInvCnt_range_map (m : Nat) (g : Nat → Nat) :
    listInvCnt ((List.range m).map g) =
    sumNat (List.range m) (fun i =>
      (List.range m).countP (fun j => decide (i < j) && decide (g j < g i))) := by
  induction m generalizing g with
  | zero => simp [listInvCnt, sumNat]
  | succ k ih =>
    have hhead :
        ((List.range (k + 1)).map g) = g 0 :: (List.range k).map (fun t => g (t + 1)) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      rfl
    have hcnt0 :
        ((List.range k).map (fun t => g (t + 1))).countP (fun b => decide (b < g 0)) =
        (List.range k).countP (fun t => decide (g (t + 1) < g 0)) := by
      rw [List.countP_map]
      rfl
    have hr0 :
        (List.range (k + 1)).countP (fun j => decide (0 < j) && decide (g j < g 0)) =
        (List.range k).countP (fun t => decide (g (t + 1) < g 0)) := by
      rw [List.range_succ_eq_map, List.countP_cons, List.countP_map]
      simp only [Nat.lt_irrefl, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      have hfn :
          ((fun j => decide (0 < j) && decide (g j < g 0)) ∘ Nat.succ) =
          (fun t => decide (g (t + 1) < g 0)) := by
        funext t
        have : 0 < Nat.succ t := Nat.succ_pos t
        simp [this]
      rw [hfn]
    have hrs :
        sumNat (List.range (k + 1))
          (fun i => (List.range (k + 1)).countP (fun j => decide (i < j) && decide (g j < g i))) =
        (List.range k).countP (fun t => decide (g (t + 1) < g 0)) +
        sumNat (List.range k)
          (fun t => (List.range k).countP (fun s => decide (t < s) && decide (g (s + 1) < g (t + 1)))) := by
      rw [sumNat_range_succ_front k (fun i => (List.range (k + 1)).countP (fun j => decide (i < j) && decide (g j < g i)))]
      rw [hr0]
      congr 1
      apply sumNat_congr
      intro t _
      rw [List.range_succ_eq_map, List.countP_cons, List.countP_map]
      have hnt : ¬ (t + 1 < 0) := by omega
      simp only [hnt, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      have hfn :
          ((fun j => decide (t + 1 < j) && decide (g j < g (t + 1))) ∘ Nat.succ) =
          (fun s => decide (t < s) && decide (g (s + 1) < g (t + 1))) := by
        funext s
        simp only [Function.comp_def]
        by_cases hts : t < s <;> simp [hts, Nat.succ_lt_succ_iff] <;> omega
      rw [hfn]
    rw [hhead, listInvCnt, hcnt0, ih (fun t => g (t + 1)), hrs]

theorem PermFin.toList_invCnt_eq {n : Nat} (p : PermFin n) :
    listInvCnt p.toList = p.invCnt := by
  let g : Nat → Nat := fun i => if h : i < n then (p.toFun ⟨i, h⟩).val else 0
  have htoList : p.toList = (List.range n).map g := by
    unfold PermFin.toList
    rw [← finRange_map_val n, List.map_map]
    apply List.map_congr_left
    intro x _
    simp [g, x.isLt]
  rw [htoList, listInvCnt_range_map]
  unfold PermFin.invCnt
  symm
  refine sumNat_finRange_congr_range n _ (fun i =>
    (List.range n).countP (fun j => decide (i < j) && decide (g j < g i))) ?_
  intro i
  rw [← finRange_map_val n, List.countP_map, countP_eq_sumNat, countP_eq_sumNat]
  apply sumNat_congr
  intro j _
  simp only [Function.comp_def, g, i.isLt, j.isLt, ↓reduceDIte]

theorem PermFin.popInv_add_des_le_inv {n : Nat} (p : PermFin n) :
    p.popInv + desList p.toList ≤ p.invCnt := by
  unfold PermFin.popInv
  rw [← PermFin.toList_invCnt_eq p]
  exact popSortList_inv_add_des_le_inv p.toList

-- ============================================================================
-- 11. Geodesic Diameter Bounds: `d + 1 ≤ 3 * gamma` and `d ≤ 3 * ind_nu`
-- ============================================================================

private def nthOr {α : Type} (xs : List α) (i : Nat) (d : α) : α :=
  match xs, i with
  | [], _ => d
  | x :: _, 0 => x
  | _ :: rest, k + 1 => nthOr rest k d

private theorem nthOr_zero_of_head? {α : Type} (xs : List α) (u : α) (h : xs.head? = some u) :
    nthOr xs 0 u = u := by
  cases xs with
  | nil => simp at h
  | cons _ _ => simp at h; exact h

private theorem take_add_one_eq_append_nthOr {α : Type} :
    ∀ (xs : List α) (i : Nat) (_ : i < xs.length) (d : α),
      xs.take (i + 1) = xs.take i ++ [nthOr xs i d]
  | [], _, hi, _ => by simp at hi
  | _ :: _, 0, _, _ => rfl
  | _ :: rest, k + 1, hi, d => by
    simp only [List.take_succ_cons, List.cons_append]
    congr 1
    exact take_add_one_eq_append_nthOr rest k (by simp only [List.length_cons] at hi; omega) d

private theorem drop_eq_nthOr_cons {α : Type} :
    ∀ (xs : List α) (i : Nat) (_ : i < xs.length) (d : α),
      xs.drop i = nthOr xs i d :: xs.drop (i + 1)
  | [], _, hi, _ => by simp at hi
  | _ :: _, 0, _, _ => rfl
  | _ :: rest, k + 1, hi, d => by
    simp only [List.drop_succ_cons]
    exact drop_eq_nthOr_cons rest k (by simp only [List.length_cons] at hi; omega) d

private theorem append_head?_of_pos_take {α : Type} (xs suf : List α) (i : Nat) (hi : 0 < i)
    (hx : xs ≠ []) : (xs.take i ++ suf).head? = xs.head? := by
  match xs, i with
  | [], _ => exact absurd rfl hx
  | _ :: _, 0 => omega
  | _ :: _, _ + 1 => rfl

private theorem append_getLast?_ne_nil {α : Type} :
    ∀ (xs ys : List α), ys ≠ [] → (xs ++ ys).getLast? = ys.getLast?
  | [], _, _ => rfl
  | x :: rest, ys, hy => by
    have hne : rest ++ ys ≠ [] := by
      intro h
      cases rest with
      | nil => exact hy h
      | cons _ _ => cases h
    have ih := append_getLast?_ne_nil rest ys hy
    simp only [List.cons_append]
    cases hxy : rest ++ ys with
    | nil => exact absurd hxy hne
    | cons b bs =>
      have : (x :: b :: bs).getLast? = (b :: bs).getLast? := rfl
      rw [this, ← hxy]
      exact ih

private theorem drop_getLast? {α : Type} :
    ∀ (xs : List α) (i : Nat), i < xs.length → (xs.drop i).getLast? = xs.getLast?
  | [], _, hi => by simp at hi
  | _ :: _, 0, _ => rfl
  | _ :: rest, k + 1, hi => by
    simp only [List.drop_succ_cons]
    have hlen : k < rest.length := by simp only [List.length_cons] at hi; omega
    have ih := drop_getLast? rest k hlen
    cases rest with
    | nil => simp at hlen
    | cons _ _ => exact ih

private theorem length_take_le {α : Type} (xs : List α) (i : Nat) (hi : i ≤ xs.length) :
    (xs.take i).length = i := by
  simp [List.length_take, Nat.min_eq_left hi]

private theorem isWalk_take {n : Nat} (G : SimpleGraphFin n) :
    ∀ (k : Nat) (W : List (Fin n)), G.IsWalk W → G.IsWalk (W.take k)
  | 0, _, _ => by simp [SimpleGraphFin.IsWalk]
  | 1, [], _ => by simp [SimpleGraphFin.IsWalk]
  | 1, [_], _ => by simp [SimpleGraphFin.IsWalk]
  | 1, _ :: _ :: _, _ => by simp [SimpleGraphFin.IsWalk]
  | k + 2, [], _ => by simp [SimpleGraphFin.IsWalk]
  | k + 2, [_], _ => by simp [SimpleGraphFin.IsWalk]
  | k + 2, _ :: v :: rest, hw => by
    have hrest := isWalk_take G (k + 1) (v :: rest) hw.2
    simp only [List.take_succ_cons] at hrest ⊢
    exact ⟨hw.1, hrest⟩

private theorem isWalk_drop {n : Nat} (G : SimpleGraphFin n) :
    ∀ (k : Nat) (W : List (Fin n)), G.IsWalk W → G.IsWalk (W.drop k)
  | 0, _, hw => hw
  | k + 1, [], _ => by simp [SimpleGraphFin.IsWalk]
  | k + 1, [_], _ => by simp [SimpleGraphFin.IsWalk]
  | k + 1, _ :: v :: rest, hw => isWalk_drop G k (v :: rest) hw.2

private theorem isWalk_append_cons {n : Nat} (G : SimpleGraphFin n) :
    ∀ (pre suf : List (Fin n)) (a : Fin n),
      G.IsWalk (pre ++ [a]) → G.IsWalk (a :: suf) → G.IsWalk (pre ++ a :: suf)
  | [], _, _, _, hsuf => hsuf
  | [_], _, _, hpre, hsuf => ⟨hpre.1, hsuf⟩
  | _ :: v :: rest, suf, a, hpre, hsuf =>
    ⟨hpre.1, isWalk_append_cons G (v :: rest) suf a hpre.2 hsuf⟩

private theorem isWalk_nthOr_adj {n : Nat} (G : SimpleGraphFin n) (d : Fin n) :
    ∀ (W : List (Fin n)) (_ : G.IsWalk W) (i : Nat) (_ : i + 1 < W.length),
      G.adj (nthOr W i d) (nthOr W (i + 1) d) = true
  | [], _, _, hi => by simp at hi
  | [_], _, _, hi => by simp at hi
  | _ :: v :: _, hw, 0, _ => hw.1
  | _ :: v :: rest, hw, k + 1, hi =>
    isWalk_nthOr_adj G d (v :: rest) hw.2 k (by simp only [List.length_cons] at hi ⊢; omega)

private theorem drop_ne_nil_of_lt {α : Type} (xs : List α) (j : Nat) (hj : j < xs.length) :
    xs.drop j ≠ [] := by
  intro h
  have hlen : (xs.drop j).length = 0 := by simp [h]
  rw [List.length_drop] at hlen
  omega

/-- Refutes a shorter `u`-`v` walk built by splicing `W.take i` with any walk `suf` ending at `v`. -/
private theorem geodesic_splice_drop {n d : Nat} (G : SimpleGraphFin n) {u v : Fin n}
    (W : List (Fin n)) (hne : W ≠ []) (hhead : W.head? = some u) (hlast : W.getLast? = some v)
    (hw : G.IsWalk W) (hno : ¬ G.WithinDist u v (d - 1))
    (i j : Nat) (hi_lt : i < W.length) (hj : j < W.length)
    (suf : List (Fin n)) (hsuf_head : suf.head? = some (nthOr W i u))
    (hsuf_last : suf.getLast? = (W.drop j).getLast?) (hsuf_walk : G.IsWalk suf)
    (hshort : i + suf.length ≤ d) :
    False := by
  cases suf with
  | nil => simp at hsuf_head
  | cons a suf_tail =>
    simp only [List.head?_cons, Option.some.injEq] at hsuf_head
    have htake : G.IsWalk (W.take i ++ [a]) := by
      rw [hsuf_head, ← take_add_one_eq_append_nthOr W i hi_lt u]
      exact isWalk_take G (i + 1) W hw
    let W' := W.take i ++ a :: suf_tail
    have hw' : G.IsWalk W' := isWalk_append_cons G (W.take i) suf_tail a htake hsuf_walk
    have hne' : W' ≠ [] := by
      cases htk : W.take i <;> simp [W', htk]
    have hhead' : W'.head? = some u := by
      cases i with
      | zero =>
        simp only [W', List.take_zero, List.nil_append, List.head?_cons]
        rw [hsuf_head, nthOr_zero_of_head? W u hhead]
      | succ m =>
        rw [append_head?_of_pos_take W (a :: suf_tail) (m + 1) (Nat.succ_pos m) hne]
        exact hhead
    have hlast' : W'.getLast? = some v := by
      rw [append_getLast?_ne_nil (W.take i) (a :: suf_tail) (by simp)]
      rw [hsuf_last, drop_getLast? W j hj]
      exact hlast
    have hlen' : W'.length ≤ (d - 1) + 1 := by
      have hlt1 : (W.take i).length = i := length_take_le W i (Nat.le_of_lt hi_lt)
      simp only [List.length_cons] at hshort
      simp only [W', List.length_append, List.length_cons, hlt1]
      omega
    exact hno ⟨W', hne', hhead', hlast', hw', hlen'⟩

private theorem geodesic_no_repeat {n d : Nat} (G : SimpleGraphFin n) {u v : Fin n}
    (W : List (Fin n)) (hne : W ≠ []) (hhead : W.head? = some u) (hlast : W.getLast? = some v)
    (hw : G.IsWalk W) (hlen : W.length = d + 1) (hno : ¬ G.WithinDist u v (d - 1))
    (i j : Nat) (hij : i < j) (hj : j < W.length) :
    nthOr W i u ≠ nthOr W j u := by
  intro heq
  have hi_lt : i < W.length := Nat.lt_trans hij hj
  have hsuf_head : (W.drop j).head? = some (nthOr W i u) := by
    rw [drop_eq_nthOr_cons W j hj u, List.head?_cons, heq]
  have hsuf_len : i + (W.drop j).length ≤ d := by
    rw [List.length_drop]; omega
  exact geodesic_splice_drop G W hne hhead hlast hw hno i j hi_lt hj (W.drop j)
    hsuf_head rfl (isWalk_drop G j W hw) hsuf_len

private theorem geodesic_no_shortcut {n d : Nat} (G : SimpleGraphFin n) {u v : Fin n}
    (W : List (Fin n)) (hne : W ≠ []) (hhead : W.head? = some u) (hlast : W.getLast? = some v)
    (hw : G.IsWalk W) (hlen : W.length = d + 1) (hno : ¬ G.WithinDist u v (d - 1))
    (i j : Nat) (hij : i + 2 ≤ j) (hj : j < W.length) :
    G.adj (nthOr W i u) (nthOr W j u) = false := by
  apply Classical.byContradiction
  intro hadj
  have hadj' : G.adj (nthOr W i u) (nthOr W j u) = true := by
    cases hb : G.adj (nthOr W i u) (nthOr W j u) <;> simp_all
  have hi_lt : i < W.length := by omega
  have hdn : W.drop j ≠ [] := drop_ne_nil_of_lt W j hj
  have hsuf_walk : G.IsWalk (nthOr W i u :: W.drop j) := by
    rw [drop_eq_nthOr_cons W j hj u]
    exact ⟨hadj', by rw [← drop_eq_nthOr_cons W j hj u]; exact isWalk_drop G j W hw⟩
  have hsuf_last : (nthOr W i u :: W.drop j).getLast? = (W.drop j).getLast? := by
    cases hd : W.drop j with
    | nil => exact absurd hd hdn
    | cons _ _ => rfl
  have hsuf_len : i + (nthOr W i u :: W.drop j).length ≤ d := by
    simp only [List.length_cons, List.length_drop]; omega
  exact geodesic_splice_drop G W hne hhead hlast hw hno i j hi_lt hj
    (nthOr W i u :: W.drop j) rfl hsuf_last hsuf_walk hsuf_len

private theorem geodesic_no_common_dom {n d : Nat} (G : SimpleGraphFin n) {u v : Fin n}
    (W : List (Fin n)) (hne : W ≠ []) (hhead : W.head? = some u) (hlast : W.getLast? = some v)
    (hw : G.IsWalk W) (hlen : W.length = d + 1) (hno : ¬ G.WithinDist u v (d - 1))
    (x : Fin n) (i j : Nat) (hij : i + 3 ≤ j) (hj : j < W.length)
    (hi_dom : x = nthOr W i u ∨ G.adj x (nthOr W i u) = true)
    (hj_dom : x = nthOr W j u ∨ G.adj x (nthOr W j u) = true) : False := by
  rcases hi_dom with rfl | hxi <;> rcases hj_dom with heq | hxj
  · exact geodesic_no_repeat G W hne hhead hlast hw hlen hno i j (by omega) hj heq
  · have := geodesic_no_shortcut G W hne hhead hlast hw hlen hno i j (by omega) hj
    rw [hxj] at this; cases this
  · have hno_sc := geodesic_no_shortcut G W hne hhead hlast hw hlen hno i j (by omega) hj
    rw [← heq, G.symm, hxi] at hno_sc; cases hno_sc
  · have hi_lt : i < W.length := by omega
    have hdn : W.drop j ≠ [] := drop_ne_nil_of_lt W j hj
    have hix : G.adj (nthOr W i u) x = true := by rw [G.symm]; exact hxi
    have hsuf_walk : G.IsWalk (nthOr W i u :: x :: W.drop j) := by
      rw [drop_eq_nthOr_cons W j hj u]
      exact ⟨hix, ⟨hxj, by rw [← drop_eq_nthOr_cons W j hj u]; exact isWalk_drop G j W hw⟩⟩
    have hsuf_last : (nthOr W i u :: x :: W.drop j).getLast? = (W.drop j).getLast? := by
      cases hd : W.drop j with
      | nil => exact absurd hd hdn
      | cons _ _ => rfl
    have hsuf_len : i + (nthOr W i u :: x :: W.drop j).length ≤ d := by
      simp only [List.length_cons, List.length_drop]; omega
    exact geodesic_splice_drop G W hne hhead hlast hw hno i j hi_lt hj
      (nthOr W i u :: x :: W.drop j) rfl hsuf_last hsuf_walk hsuf_len

private def minTrue? (p : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | m + 1 =>
    match minTrue? p m with
    | some lo => some lo
    | none => if p m then some m else none

private theorem minTrue?_eq_none :
    ∀ (p : Nat → Bool) (m : Nat), minTrue? p m = none → ∀ i : Nat, i < m → p i = false
  | _, 0, _, _, hi => by omega
  | p, m + 1, h, i, hi => by
    simp only [minTrue?] at h
    cases hsub : minTrue? p m with
    | some _ => rw [hsub] at h; simp at h
    | none =>
      rw [hsub] at h
      cases hpm : p m with
      | true => simp [hpm] at h
      | false =>
        by_cases him : i < m
        · exact minTrue?_eq_none p m hsub i him
        · have : i = m := by omega
          subst this; exact hpm

private theorem minTrue?_eq_some :
    ∀ (p : Nat → Bool) (m lo : Nat), minTrue? p m = some lo →
      lo < m ∧ p lo = true ∧ ∀ i : Nat, i < lo → p i = false
  | _, 0, _, h => by simp [minTrue?] at h
  | p, m + 1, lo, h => by
    simp only [minTrue?] at h
    cases hsub : minTrue? p m with
    | some lo' =>
      rw [hsub] at h
      have hlo : lo' = lo := Option.some.inj h
      subst hlo
      have ih := minTrue?_eq_some p m lo' hsub
      exact ⟨Nat.lt_succ_of_lt ih.1, ih.2⟩
    | none =>
      rw [hsub] at h
      cases hpm : p m with
      | true =>
        simp [hpm] at h
        subst h
        exact ⟨Nat.lt_succ_self m, hpm, minTrue?_eq_none p m hsub⟩
      | false => simp [hpm] at h

private theorem sumNat_range_eq_zero_of_all_false (p : Nat → Bool) :
    ∀ (m : Nat), (∀ i : Nat, i < m → p i = false) →
      sumNat (List.range m) (fun i => if p i then 1 else 0) = 0
  | 0, _ => rfl
  | m + 1, hall => by
    rw [List.range_succ, sumNat_append,
      sumNat_range_eq_zero_of_all_false p m (fun i hi => hall i (Nat.lt_succ_of_lt hi))]
    have hm : p m = false := hall m (Nat.lt_succ_self m)
    simp [sumNat, hm]

private theorem sumNat_range_decide_eq_le_one (m k : Nat) :
    sumNat (List.range m) (fun i => if decide (i = k) then 1 else 0) ≤ 1 := by
  induction m with
  | zero => simp [sumNat]
  | succ m ih =>
    rw [List.range_succ, sumNat_append]
    by_cases hmk : m = k
    · subst hmk
      have h0 : sumNat (List.range m) (fun i => if decide (i = m) then 1 else 0) = 0 := by
        apply sumNat_range_eq_zero_of_all_false (fun i => decide (i = m)) m
        intro i hi
        simp [Nat.ne_of_lt hi]
      rw [h0]
      simp [sumNat]
    · simp only [sumNat, hmk, decide_false, Nat.add_zero]
      exact ih

private theorem sumNat_range_indicator_le_three (m : Nat) (p : Nat → Bool)
    (hgap : ∀ i j : Nat, i < m → j < m → p i = true → p j = true → i + 3 ≤ j → False) :
    sumNat (List.range m) (fun i => if p i then 1 else 0) ≤ 3 := by
  cases hmin : minTrue? p m with
  | none =>
    have h0 := sumNat_range_eq_zero_of_all_false p m (minTrue?_eq_none p m hmin)
    omega
  | some lo =>
    have ⟨hlo_lt, hlo_t, hlo_min⟩ := minTrue?_eq_some p m lo hmin
    let f0 := fun i => if decide (i = lo) then 1 else 0
    let f1 := fun i => if decide (i = lo + 1) then 1 else 0
    let f2 := fun i => if decide (i = lo + 2) then 1 else 0
    have hmono : sumNat (List.range m) (fun i => if p i then 1 else 0) ≤
        sumNat (List.range m) (fun i => f0 i + (f1 i + f2 i)) := by
      apply sumNat_mono
      intro i hi
      have him : i < m := List.mem_range.mp hi
      cases hpi : p i with
      | false => simp
      | true =>
        have hnotlt : ¬ i < lo := by
          intro hlt
          have hf := hlo_min i hlt
          rw [hpi] at hf; cases hf
        have hlt3 : i < lo + 3 :=
          Classical.byContradiction fun hge => hgap lo i hlo_lt him hlo_t hpi (by omega)
        simp only [↓reduceIte, f0, f1, f2]
        have hcases : i = lo ∨ i = lo + 1 ∨ i = lo + 2 := by omega
        rcases hcases with rfl | rfl | rfl <;> simp
    have hsplit : sumNat (List.range m) (fun i => f0 i + (f1 i + f2 i)) =
        sumNat (List.range m) f0 + (sumNat (List.range m) f1 + sumNat (List.range m) f2) := by
      rw [sumNat_add]
      congr 1
      exact sumNat_add _ f1 f2
    have b0 : sumNat (List.range m) f0 ≤ 1 := sumNat_range_decide_eq_le_one m lo
    have b1 : sumNat (List.range m) f1 ≤ 1 := sumNat_range_decide_eq_le_one m (lo + 1)
    have b2 : sumNat (List.range m) f2 ≤ 1 := sumNat_range_decide_eq_le_one m (lo + 2)
    omega

private theorem one_le_sumNat_of_exists {α : Type} (xs : List α) (f : α → Nat)
    (h : ∃ x ∈ xs, 1 ≤ f x) : 1 ≤ sumNat xs f := by
  induction xs with
  | nil =>
    rcases h with ⟨_, hmem, _⟩
    simp at hmem
  | cons _ rest ih =>
    rcases h with ⟨x, hmem, hx⟩
    simp only [sumNat]
    rcases List.mem_cons.mp hmem with rfl | hrest
    · omega
    · have := ih ⟨x, hrest, hx⟩; omega

private theorem sumNat_const {α : Type} (xs : List α) (c : Nat) :
    sumNat xs (fun _ => c) = c * xs.length := by
  induction xs with
  | nil => simp [sumNat]
  | cons _ rest ih =>
    simp only [sumNat, List.length_cons, ih, Nat.mul_succ, Nat.add_comm]

private theorem diameterNum_geodesic {n d : Nat} (G : SimpleGraphFin n)
    (hd : G.DiameterNum d) (hdpos : 1 ≤ d) :
    ∃ (u v : Fin n) (W : List (Fin n)),
      W ≠ [] ∧ W.head? = some u ∧ W.getLast? = some v ∧ G.IsWalk W ∧
      W.length = d + 1 ∧ ¬ G.WithinDist u v (d - 1) := by
  have hnot_all : ¬ ∀ s t : Fin n, G.WithinDist s t (d - 1) := by
    intro hall
    have hle := hd.2 (d - 1) hall
    omega
  have ⟨u, hu⟩ := Classical.not_forall.mp hnot_all
  have ⟨v, hno⟩ := Classical.not_forall.mp hu
  have ⟨W, hne, hhead, hlast, hw, hlen⟩ := hd.1 u v
  have hge : d + 1 ≤ W.length :=
    Classical.byContradiction fun hlt => hno ⟨W, hne, hhead, hlast, hw, by omega⟩
  exact ⟨u, v, W, hne, hhead, hlast, hw, by omega, hno⟩

/-- **Round-5 Infinite Graph Theorem 11a (Geodesic Domination Packing):**
    In every nonempty finite graph `G` with diameter `d` and domination number `g`,
    every vertex of a dominating set covers at most 3 vertices along any shortest path
    of length `d`, giving `d + 1 ≤ 3 * g` unconditionally over all `n ≥ 1`. -/
theorem SimpleGraphFin.connected_diam_add_one_le_three_mul_dom {n d g : Nat}
    (G : SimpleGraphFin n) (hn : 1 ≤ n)
    (hd : G.DiameterNum d) (hg : G.DominationNum g) :
    d + 1 ≤ 3 * g := by
  rcases hg with ⟨⟨D, hDdom, hDlen⟩, _⟩
  by_cases hd0 : d = 0
  · subst hd0
    have hneD : D ≠ [] := by
      intro hnil
      have hv := hDdom.2 ⟨0, hn⟩
      simp [hnil] at hv
    have hpos : 1 ≤ D.length := by
      cases D with
      | nil => exact absurd rfl hneD
      | cons _ _ => simp
    omega
  · have hdpos : 1 ≤ d := by omega
    rcases diameterNum_geodesic G hd hdpos with ⟨u, v, W, hne, hhead, hlast, hw, hlen, hno⟩
    let hit : Fin n → Nat → Bool :=
      fun x i => decide (i < W.length) && (decide (x = nthOr W i u) || G.adj x (nthOr W i u))
    have hlower : W.length ≤
        sumNat (List.range W.length) (fun i => sumNat D (fun x => if hit x i then 1 else 0)) := by
      have hconst := sumNat_const (List.range W.length) 1
      rw [List.length_range, Nat.one_mul] at hconst
      calc W.length
          = sumNat (List.range W.length) (fun _ => 1) := hconst.symm
        _ ≤ sumNat (List.range W.length) (fun i => sumNat D (fun x => if hit x i then 1 else 0)) := by
            apply sumNat_mono
            intro i hi
            have him : i < W.length := List.mem_range.mp hi
            apply one_le_sumNat_of_exists
            rcases hDdom.2 (nthOr W i u) with hinD | ⟨x, hxD, hadj⟩
            · exact ⟨nthOr W i u, hinD, by simp [hit, him]⟩
            · exact ⟨x, hxD, by simp [hit, him, hadj]⟩
    have hswap := sumNat_swap (List.range W.length) D (fun i x => if hit x i then 1 else 0)
    have hupper : sumNat D (fun x => sumNat (List.range W.length) (fun i => if hit x i then 1 else 0)) ≤
        sumNat D (fun _ => 3) := by
      apply sumNat_mono
      intro x _
      apply sumNat_range_indicator_le_three
      intro i j him hjm hpi hpj hij
      simp only [hit, him, hjm, decide_true, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq] at hpi hpj
      exact geodesic_no_common_dom G W hne hhead hlast hw hlen hno x i j hij hjm hpi hpj
    have hsum3 : sumNat D (fun _ => 3) = 3 * D.length := sumNat_const D 3
    omega

private theorem flatMap_map_pair_nodup {α : Type} (m : Nat) (f : Nat → α × α)
    (hne_pair : ∀ a : Nat, a < m → (f a).1 ≠ (f a).2)
    (hdisj : ∀ a b : Nat, a < b → b < m →
      (f a).1 ≠ (f b).1 ∧ (f a).1 ≠ (f b).2 ∧ (f a).2 ≠ (f b).1 ∧ (f a).2 ≠ (f b).2) :
    (((List.range m).map f).flatMap (fun e => [e.1, e.2])).Nodup := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.flatMap_append]
    have ihk := ih (fun a ha => hne_pair a (Nat.lt_succ_of_lt ha))
      (fun a b hab hb => hdisj a b hab (Nat.lt_succ_of_lt hb))
    simp only [List.map_singleton, List.flatMap_singleton, List.nodup_append]
    refine ⟨ihk, ?_, ?_⟩
    · have hneq := hne_pair k (Nat.lt_succ_self k)
      simp [List.nodup_cons, hneq]
    · intro x hx
      rw [List.mem_flatMap] at hx
      rcases hx with ⟨e, heM, hxe⟩
      rw [List.mem_map] at heM
      rcases heM with ⟨a, ha, rfl⟩
      have hak : a < k := List.mem_range.mp ha
      have hd := hdisj a k hak (Nat.lt_succ_self k)
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hxe hy
      rcases hy with rfl | rfl
      · rcases hxe with rfl | rfl
        · intro heq; exact hd.1 heq
        · intro heq; exact hd.2.2.1 heq
      · rcases hxe with rfl | rfl
        · intro heq; exact hd.2.1 heq
        · intro heq; exact hd.2.2.2 heq

private theorem ordEdge_mem {n : Nat} {u v z : Fin n}
    (hz : z = (SimpleGraphFin.ordEdge u v).1 ∨ z = (SimpleGraphFin.ordEdge u v).2) : z = u ∨ z = v := by
  dsimp [SimpleGraphFin.ordEdge] at hz
  split at hz
  · exact hz
  · exact Or.symm hz

private theorem ordEdge_lift_rel {n : Nat} {a1 b1 a2 b2 : Fin n}
    (h1 : (SimpleGraphFin.ordEdge a1 b1).1 = a1 ∨ (SimpleGraphFin.ordEdge a1 b1).1 = b1)
    (h2 : (SimpleGraphFin.ordEdge a1 b1).2 = a1 ∨ (SimpleGraphFin.ordEdge a1 b1).2 = b1)
    (h3 : (SimpleGraphFin.ordEdge a2 b2).1 = a2 ∨ (SimpleGraphFin.ordEdge a2 b2).1 = b2)
    (h4 : (SimpleGraphFin.ordEdge a2 b2).2 = a2 ∨ (SimpleGraphFin.ordEdge a2 b2).2 = b2)
    (P : Fin n → Fin n → Prop)
    (h11 : P a1 a2) (h12 : P a1 b2) (h21 : P b1 a2) (h22 : P b1 b2) :
    P (SimpleGraphFin.ordEdge a1 b1).1 (SimpleGraphFin.ordEdge a2 b2).1 ∧
    P (SimpleGraphFin.ordEdge a1 b1).1 (SimpleGraphFin.ordEdge a2 b2).2 ∧
    P (SimpleGraphFin.ordEdge a1 b1).2 (SimpleGraphFin.ordEdge a2 b2).1 ∧
    P (SimpleGraphFin.ordEdge a1 b1).2 (SimpleGraphFin.ordEdge a2 b2).2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases h1 with h | h <;> rcases h3 with h' | h' <;> rw [h, h'] <;> assumption
  · rcases h1 with h | h <;> rcases h4 with h' | h' <;> rw [h, h'] <;> assumption
  · rcases h2 with h | h <;> rcases h3 with h' | h' <;> rw [h, h'] <;> assumption
  · rcases h2 with h | h <;> rcases h4 with h' | h' <;> rw [h, h'] <;> assumption

/-- **Round-5 Infinite Graph Theorem 11b (Geodesic Induced-Matching Bound):**
    Every finite graph `G` with diameter `d` and induced matching number `iu` admits an
    induced matching taking every third edge `(W[3a], W[3a+1])` along a shortest path of
    length `d`, yielding `d ≤ 3 * iu` universally over all `n : Nat`. -/
theorem SimpleGraphFin.connected_diam_le_three_mul_indNu {n d iu : Nat}
    (G : SimpleGraphFin n)
    (hd : G.DiameterNum d) (hiu : G.InducedMatchingNum iu) :
    d ≤ 3 * iu := by
  by_cases hd0 : d = 0
  · subst hd0; omega
  · have hdpos : 1 ≤ d := by omega
    rcases diameterNum_geodesic G hd hdpos with ⟨u, v, W, hne, hhead, hlast, hw, hlen, hno⟩
    let k := (d + 2) / 3
    let mkPair : Nat → Fin n × Fin n := fun a =>
      SimpleGraphFin.ordEdge (nthOr W (3 * a) u) (nthOr W (3 * a + 1) u)
    let M : List (Fin n × Fin n) := (List.range k).map mkPair
    have hidx : ∀ a : Nat, a < k → 3 * a + 1 < W.length := by
      intro a ha; omega
    have hsep_lt : ∀ a b : Nat, a < b → b < k →
        let x1 := nthOr W (3 * a) u
        let y1 := nthOr W (3 * a + 1) u
        let x2 := nthOr W (3 * b) u
        let y2 := nthOr W (3 * b + 1) u
        x1 ≠ x2 ∧ x1 ≠ y2 ∧ y1 ≠ x2 ∧ y1 ≠ y2 ∧
        G.adj x1 x2 = false ∧ G.adj x1 y2 = false ∧
        G.adj y1 x2 = false ∧ G.adj y1 y2 = false := by
      intro a b hab hbk
      have hb1 : 3 * b + 1 < W.length := hidx b hbk
      have hb0 : 3 * b < W.length := by omega
      exact ⟨
        geodesic_no_repeat G W hne hhead hlast hw hlen hno (3 * a) (3 * b) (by omega) hb0,
        geodesic_no_repeat G W hne hhead hlast hw hlen hno (3 * a) (3 * b + 1) (by omega) hb1,
        geodesic_no_repeat G W hne hhead hlast hw hlen hno (3 * a + 1) (3 * b) (by omega) hb0,
        geodesic_no_repeat G W hne hhead hlast hw hlen hno (3 * a + 1) (3 * b + 1) (by omega) hb1,
        geodesic_no_shortcut G W hne hhead hlast hw hlen hno (3 * a) (3 * b) (by omega) hb0,
        geodesic_no_shortcut G W hne hhead hlast hw hlen hno (3 * a) (3 * b + 1) (by omega) hb1,
        geodesic_no_shortcut G W hne hhead hlast hw hlen hno (3 * a + 1) (3 * b) (by omega) hb0,
        geodesic_no_shortcut G W hne hhead hlast hw hlen hno (3 * a + 1) (3 * b + 1) (by omega) hb1
      ⟩
    have hpair_lt_adj : ∀ a : Nat, a < k →
        (mkPair a).1.val < (mkPair a).2.val ∧ G.adj (mkPair a).1 (mkPair a).2 = true := by
      intro a ha
      have ha1 := hidx a ha
      have hne_a := geodesic_no_repeat G W hne hhead hlast hw hlen hno (3 * a) (3 * a + 1) (by omega) ha1
      have hadj_a := isWalk_nthOr_adj G u W hw (3 * a) ha1
      dsimp only [mkPair, SimpleGraphFin.ordEdge]
      by_cases hlt : (nthOr W (3 * a) u).val < (nthOr W (3 * a + 1) u).val
      · simp [hlt, hadj_a]
      · have hv_ne : (nthOr W (3 * a) u).val ≠ (nthOr W (3 * a + 1) u).val :=
          fun hveq => hne_a (Fin.ext hveq)
        have hrev : (nthOr W (3 * a + 1) u).val < (nthOr W (3 * a) u).val := by omega
        have hadj_rev : G.adj (nthOr W (3 * a + 1) u) (nthOr W (3 * a) u) = true := by
          rw [G.symm]; exact hadj_a
        simp [hlt, hrev, hadj_rev]
    have hpair_nodup : ∀ a : Nat, a < k → (mkPair a).1 ≠ (mkPair a).2 := by
      intro a ha heq
      have hlt := (hpair_lt_adj a ha).1
      rw [heq] at hlt
      exact Nat.lt_irrefl _ hlt
    have hpair_disj : ∀ a b : Nat, a < b → b < k →
        (mkPair a).1 ≠ (mkPair b).1 ∧ (mkPair a).1 ≠ (mkPair b).2 ∧
        (mkPair a).2 ≠ (mkPair b).1 ∧ (mkPair a).2 ≠ (mkPair b).2 := by
      intro a b hab hbk
      have hs := hsep_lt a b hab hbk
      exact ordEdge_lift_rel
        (ordEdge_mem (Or.inl rfl)) (ordEdge_mem (Or.inr rfl))
        (ordEdge_mem (Or.inl rfl)) (ordEdge_mem (Or.inr rfl))
        (fun x y => x ≠ y) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1
    have hM_match : G.IsMatching M := by
      refine ⟨?_, ?_⟩
      · intro e he
        rw [List.mem_map] at he
        rcases he with ⟨a, ha, rfl⟩
        exact hpair_lt_adj a (List.mem_range.mp ha)
      · exact flatMap_map_pair_nodup k mkPair hpair_nodup hpair_disj
    have hpair_nonadj : ∀ a b : Nat, a ≠ b → a < k → b < k →
        G.adj (mkPair a).1 (mkPair b).1 = false ∧ G.adj (mkPair a).1 (mkPair b).2 = false ∧
        G.adj (mkPair a).2 (mkPair b).1 = false ∧ G.adj (mkPair a).2 (mkPair b).2 = false := by
      intro a b hne_ab ha hb
      rcases Nat.lt_or_gt_of_ne hne_ab with hab | hba
      · have hs := hsep_lt a b hab hb
        exact ordEdge_lift_rel
          (ordEdge_mem (Or.inl rfl)) (ordEdge_mem (Or.inr rfl))
          (ordEdge_mem (Or.inl rfl)) (ordEdge_mem (Or.inr rfl))
          (fun x y => G.adj x y = false) hs.2.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2
      · have hs := hsep_lt b a hba ha
        exact ordEdge_lift_rel
          (ordEdge_mem (Or.inl rfl)) (ordEdge_mem (Or.inr rfl))
          (ordEdge_mem (Or.inl rfl)) (ordEdge_mem (Or.inr rfl))
          (fun x y => G.adj x y = false)
          (by rw [G.symm]; exact hs.2.2.2.2.1) (by rw [G.symm]; exact hs.2.2.2.2.2.2.1)
          (by rw [G.symm]; exact hs.2.2.2.2.2.1) (by rw [G.symm]; exact hs.2.2.2.2.2.2.2)
    have hM_ind : G.IsInducedMatching M := by
      refine ⟨hM_match, ?_⟩
      intro e1 he1 e2 he2 hne12
      rw [List.mem_map] at he1 he2
      rcases he1 with ⟨a, ha, rfl⟩
      rcases he2 with ⟨b, hb, rfl⟩
      have hne_ab : a ≠ b := fun heq => hne12 (by subst heq; rfl)
      exact hpair_nonadj a b hne_ab (List.mem_range.mp ha) (List.mem_range.mp hb)
    have hlen_M : k ≤ iu := by
      have h := hiu.2 M hM_ind
      simpa [M] using h
    omega

-- ============================================================================
-- Round-6 Section 12: promoted Round-5 candidate theorems (Track A)
--
-- Candidate tags from `novelty_audit_r5.json` promoted here:
--   T4: r5_G_C4TF_1min_deg<=1gamma+0    [CONNECTED, C4_FREE, TRIANGLE_FREE] min_deg <= gamma
-- ============================================================================

namespace R6Helpers

theorem list_length_le_of_forall_mem {α : Type} [DecidableEq α] :
    ∀ (L D : List α), L.Nodup → D.Nodup → (∀ x ∈ L, x ∈ D) → L.length ≤ D.length
  | [], _, _, _, _ => Nat.zero_le _
  | x :: L', D, hL, hD, hsub => by
    rw [List.nodup_cons] at hL
    rcases hL with ⟨hxL', hL'nd⟩
    have hxD : x ∈ D := hsub x (by simp)
    have hsub' : ∀ y ∈ L', y ∈ D.erase x := by
      intro y hy
      have hyD : y ∈ D := hsub y (by simp [hy])
      have hyx : y ≠ x := fun h => hxL' (h ▸ hy)
      exact (List.mem_erase_of_ne (a := y) (b := x) hyx).mpr hyD
    have ih := list_length_le_of_forall_mem L' (D.erase x) hL'nd (hD.erase x) hsub'
    have hpos : 1 ≤ D.length := List.length_pos_of_mem hxD
    have hlen : (D.erase x).length = D.length - 1 := List.length_erase_of_mem hxD
    have hs : L'.length + 1 ≤ (D.erase x).length + 1 := Nat.succ_le_succ ih
    rw [hlen, Nat.sub_add_cancel hpos] at hs
    simpa only [List.length_cons] using hs

theorem list_length_le_finRange {n : Nat} (L : List (Fin n)) (hnd : L.Nodup) :
    L.length ≤ n := by
  have h := list_length_le_of_forall_mem L (List.finRange n) hnd
    (List.nodup_finRange n) (fun x _ => List.mem_finRange x)
  simpa using h

theorem list_length_eq_finRange {n : Nat} (D : List (Fin n))
    (hnd : D.Nodup) (hall : ∀ v : Fin n, v ∈ D) : D.length = n := by
  have h1 : D.length ≤ n := list_length_le_finRange D hnd
  have h2 : n ≤ D.length := by
    have h := list_length_le_of_forall_mem (List.finRange n) D
      (List.nodup_finRange n) hnd (fun x _ => hall x)
    simpa using h
  omega

theorem nodup_map_of_inj {α β : Type} (f : α → β) :
    ∀ (L : List α), L.Nodup → (∀ a ∈ L, ∀ b ∈ L, f a = f b → a = b) → (L.map f).Nodup
  | [], _, _ => by simp
  | x :: L', hnd, hinj => by
    rw [List.nodup_cons] at hnd
    rcases hnd with ⟨hxL', hL'nd⟩
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_of_inj f L' hL'nd (fun a ha b hb => hinj a (by simp [ha]) b (by simp [hb]))⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨y, hyL', hyf⟩
    have hyx : y = x := hinj y (by simp [hyL']) x (by simp) hyf
    exact hxL' (hyx ▸ hyL')

/-- Turns the `Bool` negation shape produced by `!(...)` in the `CombDefs` predicates
into a usable `Prop` negation. -/
theorem not_of_bnot_decide {p : Prop} [Decidable p] (h : (!decide p) = true) : ¬ p := by
  intro hp
  rw [decide_eq_true hp] at h
  exact absurd h (by simp)

end R6Helpers

namespace SimpleGraphFin

/-- **Round-6 Lemma (neighbourhood injection):** for `C_4`-free triangle-free `G` and a
dominating set `D`, every vertex `v` outside `D` admits an injection from `N(v)` into `D`,
hence `deg v ≤ |D|`. -/
theorem deg_le_length_of_not_mem {n : Nat} (G : SimpleGraphFin n)
    (hTF : G.TriangleFree) (hC4 : G.C4Free)
    (D : List (Fin n)) (hnd : D.Nodup)
    (hcov : ∀ v : Fin n, v ∈ D ∨ ∃ u ∈ D, G.adj u v = true)
    (v : Fin n) (hv : v ∉ D) : G.deg v ≤ D.length := by
  classical
  have hdom_exists : ∀ w : Fin n, G.adj v w = true →
      ∃ u : Fin n, u ∈ D ∧ (u = w ∨ G.adj u w = true) := by
    intro w _
    rcases hcov w with hw | ⟨u, huD, huw⟩
    · exact ⟨w, hw, Or.inl rfl⟩
    · exact ⟨u, huD, Or.inr huw⟩
  let g : Fin n → Fin n := fun w =>
    if h : G.adj v w = true then Classical.choose (hdom_exists w h) else w
  have hg_mem : ∀ w, G.adj v w = true → g w ∈ D := by
    intro w haw
    simp only [g]
    split
    next h => exact (Classical.choose_spec (hdom_exists w h)).1
    next h => exact absurd haw h
  have hg_dom : ∀ w, g w = w ∨ G.adj (g w) w = true := by
    intro w
    simp only [g]
    split
    next h => exact (Classical.choose_spec (hdom_exists w h)).2
    next _ => exact Or.inl rfl
  have hg_inj : ∀ a b, G.adj v a = true → G.adj v b = true → g a = g b → a = b := by
    intro a b ha hb heq
    by_cases hab : a = b
    · exact hab
    have hua_mem : g a ∈ D := hg_mem a ha
    have hnva : a ≠ v := fun h => by rw [h] at ha; rw [G.loopless v] at ha; exact Bool.noConfusion ha
    have hnvb : b ≠ v := fun h => by rw [h] at hb; rw [G.loopless v] at hb; exact Bool.noConfusion hb
    have hnvu : g a ≠ v := fun h => hv (h ▸ hua_mem)
    rcases hg_dom a with hga | hga <;> rcases hg_dom b with hgb | hgb
    · rw [hga, hgb] at heq
      exact heq
    · have hba : G.adj a b = true := by
        have h := hgb
        rw [← heq] at h
        rw [hga] at h
        exact h
      exact absurd ⟨ha, hba, hb⟩ (R6Helpers.not_of_bnot_decide (hTF v a b))
    · have hba : G.adj b a = true := by
        have h := hga
        rw [heq] at h
        rw [hgb] at h
        exact h
      exact absurd ⟨hb, hba, ha⟩ (R6Helpers.not_of_bnot_decide (hTF v b a))
    · have hua : G.adj (g a) a = true := hga
      have hub : G.adj (g a) b = true := by
        have h := hgb
        rw [← heq] at h
        exact h
      have hne_ua : g a ≠ a := fun h => by
        rw [h, G.loopless a] at hua; exact Bool.noConfusion hua
      have hne_ub : g a ≠ b := fun h => by
        rw [h, G.loopless b] at hub; exact Bool.noConfusion hub
      by_cases hab_adj : G.adj a b = true
      · exact absurd ⟨hua, hab_adj, hub⟩ (R6Helpers.not_of_bnot_decide (hTF (g a) a b))
      · exact absurd ⟨by rw [G.symm]; exact ha, hb, by rw [G.symm]; exact hub, hua⟩
          (R6Helpers.not_of_bnot_decide
            (hC4 a v b (g a) hnva hab (Ne.symm hne_ua) (Ne.symm hnvb) (Ne.symm hnvu) (Ne.symm hne_ub)))
  let L := (List.finRange n).filter (fun w => G.adj v w)
  have hLnd : L.Nodup := (List.nodup_finRange n).filter _
  have hdeg : G.deg v = L.length := by
    simp only [SimpleGraphFin.deg, L, List.countP_eq_length_filter]
  have hmapnd : (L.map g).Nodup := by
    refine R6Helpers.nodup_map_of_inj g L hLnd ?_
    intro a ha b hb
    exact hg_inj a b (List.mem_filter.mp ha).2 (List.mem_filter.mp hb).2
  have hsubmem : ∀ z ∈ L.map g, z ∈ D := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
    exact hg_mem w (List.mem_filter.mp hw).2
  have hle := R6Helpers.list_length_le_of_forall_mem (L.map g) D hmapnd hnd hsubmem
  rw [List.length_map] at hle
  omega

/-- **Round-6 Infinite Graph Theorem 12 (C4-free + triangle-free domination bound):**
    In every nonempty finite graph `G` that is triangle-free and `C_4`-free, the minimum
    degree is at most the domination number: `min_deg <= gamma`, universally over all
    `n k : Nat`. Promotes Round-5 candidate `r5_G_C4TF_1min_deg<=1gamma+0`. -/
theorem minDeg_le_dom_of_c4free_triangleFree {n k : Nat}
    (G : SimpleGraphFin n) (hn : 1 ≤ n)
    (hTF : G.TriangleFree) (hC4 : G.C4Free)
    (hk : G.DominationNum k) : G.minDeg ≤ k := by
  classical
  rcases hk with ⟨⟨D, hDdom, hDlen⟩, _⟩
  rcases hDdom with ⟨hnd, hcov⟩
  have h0n : 0 < n := hn
  by_cases hex : ∃ v : Fin n, v ∉ D
  · rcases hex with ⟨v, hv⟩
    have h1 : G.deg v ≤ D.length := deg_le_length_of_not_mem G hTF hC4 D hnd hcov v hv
    have h2 : G.minDeg ≤ G.deg v := G.minDeg_le_deg h0n v
    omega
  · have hall : ∀ v : Fin n, v ∈ D := fun v =>
      Classical.byContradiction (fun hv => hex ⟨v, hv⟩)
    have hlen : D.length = n := R6Helpers.list_length_eq_finRange D hnd hall
    let x : Fin n := ⟨0, h0n⟩
    have hxmem : x ∈ List.finRange n := List.mem_finRange x
    have hLer : ((List.finRange n).filter (fun w => G.adj x w)).length ≤
        ((List.finRange n).erase x).length := by
      apply R6Helpers.list_length_le_of_forall_mem
      · exact (List.nodup_finRange n).filter _
      · exact (List.nodup_finRange n).erase x
      · intro y hy
        rcases List.mem_filter.mp hy with ⟨hyfin, hyadj⟩
        have hyne : y ≠ x := fun h => by
          rw [h, G.loopless x] at hyadj
          exact Bool.noConfusion hyadj
        exact (List.mem_erase_of_ne (a := y) (b := x) hyne).mpr hyfin
    have herase_len : ((List.finRange n).erase x).length = n - 1 := by
      rw [List.length_erase_of_mem hxmem, List.length_finRange]
    have hdegx : G.deg x ≤ n - 1 := by
      have hdx : G.deg x = ((List.finRange n).filter (fun w => G.adj x w)).length := by
        simp only [SimpleGraphFin.deg, List.countP_eq_length_filter]
      omega
    have h2 : G.minDeg ≤ G.deg x := G.minDeg_le_deg h0n x
    omega

end SimpleGraphFin

-- ============================================================================
-- Round-6 Section 13: geodesic off-path counting (Track A, T6)
--
-- Candidate tag promoted here:
--   T6: r5_G_CONN_1diam+1min_deg<=n     [CONNECTED] diam + min_deg <= n
--
-- Proof: let `W` be a geodesic of length `d` and `x` its first vertex, `y` its second.
-- Every neighbour of `x` is `y` or lies off the path (any other path neighbour would
-- shortcut the geodesic), so `delta <= deg x <= 1 + |off-path|`; the `d + 1` path
-- vertices are pairwise distinct, so `n = (d + 1) + |off-path|` and `d + delta <= n`.
-- ============================================================================

namespace R6Helpers

theorem sumNat_indicator_eq_zero {α : Type} [DecidableEq α]
    (xs : List α) (v : α) (hnot : v ∉ xs) :
    sumNat xs (fun y => if y = v then 1 else 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons r rs ih =>
    simp only [sumNat]
    have hrv : r ≠ v := fun h => hnot (by simp [h])
    have hrs := ih (fun hm => hnot (by simp [hm]))
    simp [hrv, hrs]

theorem sumNat_indicator_eq_one {α : Type} [DecidableEq α]
    (xs : List α) (hnd : xs.Nodup) (v : α) (hv : v ∈ xs) :
    sumNat xs (fun y => if y = v then 1 else 0) = 1 := by
  induction xs with
  | nil => simp at hv
  | cons x rest ih =>
    simp only [sumNat]
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hv with hvx | hvr
    · subst hvx
      have hzero := sumNat_indicator_eq_zero rest v hnd.1
      simp [hzero]
    · have hvx : x ≠ v := fun h => hnd.1 (h ▸ hvr)
      have hr := ih hnd.2 hvr
      simp [hvx, hr]

theorem countP_mem_eq_length {n : Nat} (W : List (Fin n)) (hnd : W.Nodup) :
    (List.finRange n).countP (fun x => decide (x ∈ W)) = W.length := by
  rw [countP_eq_sumNat]
  have hcongr : sumNat (List.finRange n) (fun x => if decide (x ∈ W) then 1 else 0)
      = sumNat (List.finRange n) (fun x => sumNat W (fun y => if y = x then 1 else 0)) := by
    apply sumNat_congr
    intro x _
    by_cases hx : x ∈ W
    · have h1 : sumNat W (fun y => if y = x then 1 else 0) = 1 :=
        sumNat_indicator_eq_one W hnd x hx
      simp [hx, h1]
    · have h0 : sumNat W (fun y => if y = x then 1 else 0) = 0 :=
        sumNat_indicator_eq_zero W x (fun hmem => hx hmem)
      simp [hx, h0]
  rw [hcongr, sumNat_swap]
  have h1 : sumNat W (fun y => sumNat (List.finRange n) (fun x => if y = x then 1 else 0))
      = sumNat W (fun _ => 1) := by
    apply sumNat_congr
    intro y _
    have e1 : sumNat (List.finRange n) (fun x => if x = y then 1 else 0) = 1 :=
      sumNat_indicator_eq_one (List.finRange n) (List.nodup_finRange n) y (List.mem_finRange y)
    have e2 : sumNat (List.finRange n) (fun x => if y = x then 1 else 0)
        = sumNat (List.finRange n) (fun x => if x = y then 1 else 0) := by
      apply sumNat_congr
      intro x _
      by_cases h : y = x
      · simp [h]
      · have h' : ¬ x = y := fun hh => h hh.symm
        simp [h, h']
    rw [e2, e1]
  rw [h1, sumNat_const]
  simp

theorem countP_notMem_eq_sub {n : Nat} (W : List (Fin n)) (hnd : W.Nodup) :
    (List.finRange n).countP (fun x => !decide (x ∈ W)) = n - W.length := by
  have hmem := countP_mem_eq_length W hnd
  have hsplit : (List.finRange n).countP (fun x => decide (x ∈ W)) +
      (List.finRange n).countP (fun x => !decide (x ∈ W)) = n := by
    rw [countP_eq_sumNat, countP_eq_sumNat, ← sumNat_add]
    have h1 : sumNat (List.finRange n)
        (fun x => (if decide (x ∈ W) then 1 else 0) + (if !decide (x ∈ W) then 1 else 0))
        = sumNat (List.finRange n) (fun _ => 1) := by
      apply sumNat_congr
      intro x _
      cases decide (x ∈ W) <;> simp
    rw [h1, sumNat_const]
    simp
  omega

theorem nthOr_eq_getElem {α : Type} :
    ∀ (xs : List α) (d : α) (i : Nat) (hi : i < xs.length), nthOr xs i d = xs[i]
  | [], _, _, hi => by simp at hi
  | a :: rest, d, 0, _ => rfl
  | a :: rest, d, k + 1, hi => by
    have hk : k < rest.length := by simp only [List.length_cons] at hi; omega
    have ih := nthOr_eq_getElem rest d k hk
    show nthOr rest k d = (a :: rest)[k + 1]
    rw [ih]
    simp

end R6Helpers

namespace SimpleGraphFin

theorem deg_le_pred {n : Nat} (G : SimpleGraphFin n) (_hn : 1 ≤ n) (x : Fin n) :
    G.deg x ≤ n - 1 := by
  have hxmem : x ∈ List.finRange n := List.mem_finRange x
  have hLer : ((List.finRange n).filter (fun w => G.adj x w)).length ≤
      ((List.finRange n).erase x).length := by
    apply R6Helpers.list_length_le_of_forall_mem
    · exact (List.nodup_finRange n).filter _
    · exact (List.nodup_finRange n).erase x
    · intro y hy
      rcases List.mem_filter.mp hy with ⟨hyfin, hyadj⟩
      have hyne : y ≠ x := fun h => by
        rw [h, G.loopless x] at hyadj
        exact Bool.noConfusion hyadj
      exact (List.mem_erase_of_ne (a := y) (b := x) hyne).mpr hyfin
  have herase : ((List.finRange n).erase x).length = n - 1 := by
    rw [List.length_erase_of_mem hxmem, List.length_finRange]
  have hdx : G.deg x = ((List.finRange n).filter (fun w => G.adj x w)).length := by
    simp only [SimpleGraphFin.deg, List.countP_eq_length_filter]
  omega

/-- **Round-6 Infinite Graph Theorem 13 (diameter + minimum degree):**
    In every nonempty finite graph `G` with diameter `d`, `d + min_deg <= n`, universally
    over all `n : Nat`. Promotes Round-5 candidate `r5_G_CONN_1diam+1min_deg<=n+0`. -/
theorem diam_add_minDeg_le {n d : Nat}
    (G : SimpleGraphFin n) (hn : 1 ≤ n) (hd : G.DiameterNum d) :
    d + G.minDeg ≤ n := by
  classical
  by_cases hd0 : d = 0
  · subst hd0
    have h1 : G.minDeg ≤ G.deg ⟨0, hn⟩ := G.minDeg_le_deg hn ⟨0, hn⟩
    have h2 : G.deg ⟨0, hn⟩ ≤ n - 1 := G.deg_le_pred hn ⟨0, hn⟩
    omega
  · have hdpos : 1 ≤ d := by omega
    rcases diameterNum_geodesic G hd hdpos with ⟨u, v, W, hne, hhead, hlast, hw, hlen, hno⟩
    have hWnd : W.Nodup := by
      rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
      intro i j hi hj hij
      have h1 : nthOr W i u = W[i] := R6Helpers.nthOr_eq_getElem W u i hi
      have h2 : nthOr W j u = W[j] := R6Helpers.nthOr_eq_getElem W u j hj
      rw [← h1, ← h2]
      exact geodesic_no_repeat G W hne hhead hlast hw hlen hno i j hij hj
    have hoff : (List.finRange n).countP (fun x => !decide (x ∈ W)) = n - W.length :=
      R6Helpers.countP_notMem_eq_sub W hWnd
    let x0 : Fin n := nthOr W 0 u
    let x1 : Fin n := nthOr W 1 u
    have hx0 : x0 = u := nthOr_zero_of_head? W u hhead
    have h1lt : 1 < W.length := by omega
    have hx1 : nthOr W 1 u = W[1] := R6Helpers.nthOr_eq_getElem W u 1 h1lt
    -- every neighbour of `x0` is `x1` or off the path
    have hnb : ∀ w : Fin n, G.adj x0 w = true → w ≠ x1 → w ∉ W := by
      intro w haw hne1 hwin
      rcases List.mem_iff_getElem.mp hwin with ⟨j, hj, hWj⟩
      have hju : nthOr W j u = w := by
        rw [R6Helpers.nthOr_eq_getElem W u j hj]
        exact hWj
      rcases j with _ | j1
      · -- `j = 0`: the neighbour would be `x0` itself
        have hW0 : W[0] = u := by
          rw [← nthOr_zero_of_head? W u hhead]
          exact (R6Helpers.nthOr_eq_getElem W u 0 (by omega)).symm
        have hw0 : w = u := by rw [← hWj, hW0]
        rw [hw0] at haw
        rw [hx0] at haw
        rw [G.loopless u] at haw
        exact Bool.noConfusion haw
      · rcases j1 with _ | k
        · -- `j = 1`: the neighbour is the second path vertex
          exact hne1 (by dsimp only [x1]; rw [← hWj]; exact hx1.symm)
        · -- `j >= 2`: a shortcut would contradict geodesicity
          have hsc := geodesic_no_shortcut G W hne hhead hlast hw hlen hno 0 (k + 2) (by omega) hj
          have e1 : nthOr W 0 u = x0 := rfl
          have hsc2 : G.adj x0 w = false := by simpa [e1, hju] using hsc
          rw [hsc2] at haw
          exact Bool.noConfusion haw
    -- degree bound
    have hdegb : G.deg x0 ≤ 1 + (n - W.length) := by
      rw [SimpleGraphFin.deg, countP_eq_sumNat]
      have hstep1 : sumNat (List.finRange n) (fun w => if G.adj x0 w then 1 else 0) ≤
          sumNat (List.finRange n) (fun w => if (w = x1 ∨ w ∉ W) then 1 else 0) := by
        apply sumNat_mono
        intro w _
        by_cases haw : G.adj x0 w = true
        · by_cases h1 : w = x1
          · subst h1
            simp [haw]
          · have h2 := hnb w haw h1
            simp [haw, h1, h2]
        · simp [haw]
      have hstep2 : sumNat (List.finRange n) (fun w => if (w = x1 ∨ w ∉ W) then 1 else 0) ≤
          sumNat (List.finRange n) (fun w => if w = x1 then 1 else 0) +
            (List.finRange n).countP (fun w => !decide (w ∈ W)) := by
        rw [countP_eq_sumNat]
        rw [← sumNat_add]
        apply sumNat_mono
        intro w _
        by_cases h1 : w = x1 <;> by_cases h2 : w ∈ W <;> simp [h1, h2]
      have hone : sumNat (List.finRange n) (fun w => if w = x1 then 1 else 0) = 1 :=
        R6Helpers.sumNat_indicator_eq_one (List.finRange n) (List.nodup_finRange n) x1
          (List.mem_finRange x1)
      omega
    have hmd : G.minDeg ≤ G.deg x0 := G.minDeg_le_deg (by omega) x0
    have hmemcnt : (List.finRange n).countP (fun x => decide (x ∈ W)) = W.length :=
      R6Helpers.countP_mem_eq_length W hWnd
    have hWle : W.length ≤ n := by
      rw [← hmemcnt]
      have hcl := List.countP_le_length (p := fun x => decide (x ∈ W)) (l := List.finRange n)
      simpa using hcl
    omega

end SimpleGraphFin

-- ============================================================================
-- 14. Solution of Open Conjecture `Conj_AllPerms_StackDes_Le_Peaks`:
--     `des(S(p)) <= peaks(p)` for all `p : PermFin n`
-- ============================================================================

private theorem desList_eq_zero_of_pairwise :
    ∀ (xs : List Nat), xs.Pairwise (· ≤ ·) → desList xs = 0
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, hpw => by
    cases hpw with
    | cons ha hrest =>
      have hab : a ≤ b := ha b (by simp)
      have hn : ¬ (a > b) := by omega
      simp only [desList, hn, ↓reduceIte, Nat.zero_add]
      exact desList_eq_zero_of_pairwise (b :: rest) hrest

private theorem desList_append_le :
    ∀ (p out : List Nat), p.Pairwise (· ≤ ·) → desList (p ++ out) ≤ 1 + desList out
  | [], out, _ => by simp [Nat.le_add_left]
  | [a], [], _ => by simp [desList]
  | [a], y :: r, _ => by
    simp only [List.singleton_append, desList]
    by_cases hgt : a > y
    · simp [hgt]
    · simp [hgt]
  | a :: b :: rest, out, hpw => by
    cases hpw with
    | cons ha hrest =>
      have hab : a ≤ b := ha b (by simp)
      have hn : ¬ (a > b) := by omega
      simp only [List.cons_append, desList, hn, ↓reduceIte, Nat.zero_add]
      exact desList_append_le (b :: rest) out hrest

private theorem desList_append_cons_of_lt :
    ∀ (p t : List Nat) (x : Nat),
      p.Pairwise (· ≤ ·) → (∀ s ∈ p, s < x) → desList (p ++ x :: t) = desList (x :: t)
  | [], _, _, _, _ => rfl
  | [a], t, x, _, hlt => by
    have hax : a < x := hlt a (by simp)
    have hn : ¬ (a > x) := by omega
    simp [desList, hn]
  | a :: b :: rest, t, x, hpw, hlt => by
    cases hpw with
    | cons ha hrest =>
      have hab : a ≤ b := ha b (by simp)
      have hn : ¬ (a > b) := by omega
      simp only [List.cons_append, desList, hn, ↓reduceIte, Nat.zero_add]
      exact desList_append_cons_of_lt (b :: rest) t x hrest (fun s hs => hlt s (by simp [hs]))

private theorem nodup_westStep_append (stk rest : List Nat) (x : Nat) (stk_rem : List Nat)
    (hsplit : stk = (westStep stk x).1 ++ stk_rem)
    (hstk2 : (westStep stk x).2 = x :: stk_rem)
    (hnd : (stk ++ x :: rest).Nodup) :
    ((westStep stk x).2 ++ rest).Nodup := by
  rw [hstk2]
  rw [List.nodup_append] at hnd
  rcases hnd with ⟨hstk_nd, hxr_nd, hdisj⟩
  rw [List.nodup_cons] at hxr_nd
  rcases hxr_nd with ⟨hxrest, hrest_nd⟩
  have hsub : stk_rem.Sublist stk := by
    rw [hsplit]
    exact List.sublist_append_right _ _
  have hrem_nd : stk_rem.Nodup := hsub.nodup hstk_nd
  have hxrem : x ∉ stk_rem := fun hx => hdisj x (hsub.subset hx) x (by simp) rfl
  rw [List.nodup_append]
  refine ⟨(List.nodup_cons.mpr ⟨hxrem, hrem_nd⟩), hrest_nd, ?_⟩
  intro a ha b hb heq
  subst heq
  rcases List.mem_cons.mp ha with rfl | harem
  · exact hxrest hb
  · exact hdisj a (hsub.subset harem) a (by simp [hb]) rfl

private theorem listPeaksCnt_le_cons (a b : Nat) (r : List Nat) :
    listPeaksCnt (b :: r) ≤ listPeaksCnt (a :: b :: r) := by
  cases r with
  | nil => simp [listPeaksCnt]
  | cons c t => simp [listPeaksCnt]

private theorem westSortAux_des_le_peaks :
    ∀ (xs stk : List Nat),
      stk.Pairwise (· ≤ ·) → (stk ++ xs).Nodup →
      desList (westSortAux xs stk) ≤
        listPeaksCnt ((match stk with | [] => [] | s0 :: _ => [s0]) ++ xs)
  | [], stk, hpw, _ => by
    simp only [westSortAux, desList_eq_zero_of_pairwise stk hpw]
    exact Nat.zero_le _
  | x :: rest, [], _, hnd => by
    simp only [westSortAux, westStep, List.nil_append]
    exact westSortAux_des_le_peaks rest [x] (List.pairwise_singleton _ _) (by simpa using hnd)
  | x :: rest, s0 :: st, hpw, hnd => by
    have hsx_ne : s0 ≠ x := by
      rw [List.nodup_append] at hnd
      exact hnd.2.2 s0 (by simp) x (by simp)
    by_cases hlt : s0 < x
    · rcases westStep_spec (s0 :: st) x hpw with ⟨stk_rem, hsplit, hstk2, hpop_lt, _, hpop_pw, hpw2⟩
      have hnd2 : ((westStep (s0 :: st) x).2 ++ rest).Nodup :=
        nodup_westStep_append (s0 :: st) rest x stk_rem hsplit hstk2 hnd
      have ih := westSortAux_des_le_peaks rest (westStep (s0 :: st) x).2 hpw2 hnd2
      rw [hstk2] at ih
      simp only [List.singleton_append] at ih ⊢
      have hwa : westSortAux (x :: rest) (s0 :: st) =
          (westStep (s0 :: st) x).1 ++ westSortAux rest (westStep (s0 :: st) x).2 := rfl
      rw [hwa]
      cases rest with
      | nil =>
        rw [hstk2, westSortAux, desList_append_cons_of_lt _ stk_rem x hpop_pw hpop_lt]
        have hz : desList (x :: stk_rem) = 0 := by
          apply desList_eq_zero_of_pairwise
          rw [← hstk2]; exact hpw2
        omega
      | cons y rest2 =>
        have hxy_ne : x ≠ y := by
          rw [List.nodup_append] at hnd
          have hr_nd := hnd.2.1
          rw [List.nodup_cons] at hr_nd
          exact fun heq => hr_nd.1 (heq ▸ by simp)
        by_cases hyx : y < x
        · have hle_app := desList_append_le (westStep (s0 :: st) x).1 (westSortAux (y :: rest2) (westStep (s0 :: st) x).2) hpop_pw
          rw [← hstk2] at ih
          have hpeak : listPeaksCnt (s0 :: x :: y :: rest2) = 1 + listPeaksCnt (x :: y :: rest2) := by
            simp [listPeaksCnt, hlt, hyx, Nat.add_comm]
          omega
        · have hxy : x < y := by omega
          have hwxy : westSortAux (y :: rest2) (x :: stk_rem) =
              x :: ((westStep stk_rem y).1 ++ westSortAux rest2 (westStep stk_rem y).2) := by
            simp [westSortAux, westStep, hxy]
          rw [← hstk2] at ih
          rw [hstk2, hwxy, desList_append_cons_of_lt _ _ x hpop_pw hpop_lt, ← hwxy, ← hstk2]
          have hmono := listPeaksCnt_le_cons s0 x (y :: rest2)
          omega
    · have hstep : westStep (s0 :: st) x = ([], x :: s0 :: st) := by
        simp [westStep, hlt]
      have hpw2 : (x :: s0 :: st).Pairwise (· ≤ ·) := by
        cases hpw with
        | cons ha hrest =>
          refine .cons (fun z hz => ?_) (.cons ha hrest)
          rcases List.mem_cons.mp hz with rfl | hzm
          · omega
          · have := ha z hzm; omega
      have hnd2 : ((x :: s0 :: st) ++ rest).Nodup := by
        rw [List.nodup_append] at hnd ⊢
        rcases hnd with ⟨h1, h2, h3⟩
        rw [List.nodup_cons] at h2
        refine ⟨List.nodup_cons.mpr ⟨fun hx => h3 x hx x (by simp) rfl, h1⟩, h2.2, ?_⟩
        intro a ha b hb
        rcases List.mem_cons.mp ha with rfl | ham
        · exact fun heq => h2.1 (heq ▸ hb)
        · exact h3 a ham b (by simp [hb])
      have ih := westSortAux_des_le_peaks rest (x :: s0 :: st) hpw2 hnd2
      simp only [westSortAux, hstep, List.nil_append, List.singleton_append] at ih ⊢
      have hmono := listPeaksCnt_le_cons s0 x rest
      omega

theorem westSortList_des_le_peaks (xs : List Nat) (hnodup : xs.Nodup) :
    desList (westSortList xs) ≤ listPeaksCnt xs := by
  have h := westSortAux_des_le_peaks xs [] .nil (by simpa using hnodup)
  simpa [westSortList] using h

private theorem permFin_toList_nodup {n : Nat} (p : PermFin n) : p.toList.Nodup := by
  unfold PermFin.toList
  apply R6Helpers.nodup_map_of_inj _ (List.finRange n) (List.nodup_finRange n)
  intro a _ b _ hval
  exact p.toFun_inj (Fin.ext hval)

/-- **Round-6/8 Theorem 14 (Solution to `Conj_AllPerms_StackDes_Le_Peaks`):**
    Every permutation `p : PermFin n` satisfies `p.stackDes ≤ p.peaksCnt`, proved
    universally over all `n : Nat`. -/
theorem PermFin.stackDes_le_peaksCnt {n : Nat} (p : PermFin n) :
    p.stackDes ≤ p.peaksCnt :=
  westSortList_des_le_peaks p.toList (permFin_toList_nodup p)

-- ============================================================================
-- 15. West Stack-Sorting Preserves Strictly Increasing Subsequences (`lis <= stack_lis`)
-- ============================================================================

private theorem sublist_split_append {α : Type} :
    ∀ {xs ys sub : List α}, sub.Sublist (xs ++ ys) →
      ∃ s1 s2, sub = s1 ++ s2 ∧ s1.Sublist xs ∧ s2.Sublist ys
  | [], ys, sub, h => ⟨[], sub, rfl, .slnil, h⟩
  | x :: xt, ys, sub, h => by
    simp only [List.cons_append] at h
    cases h with
    | cons _ h' =>
      rcases sublist_split_append (xs := xt) h' with ⟨s1, s2, heq, hs1, hs2⟩
      exact ⟨s1, s2, heq, .cons x hs1, hs2⟩
    | cons_cons _ h' =>
      rcases sublist_split_append (xs := xt) h' with ⟨s1, s2, heq, hs1, hs2⟩
      exact ⟨x :: s1, s2, by rw [heq]; rfl, .cons_cons x hs1, hs2⟩

private theorem sublist_cons_cons_of_sublist {α : Type} {x : α} {xs stk_rem sub : List α}
    (h : sub.Sublist (x :: xs)) :
    sub.Sublist (x :: (stk_rem ++ xs)) := by
  cases h with
  | cons _ h' =>
    exact List.Sublist.cons x (List.Sublist.trans h' (List.sublist_append_right stk_rem xs))
  | cons_cons _ h' =>
    exact List.Sublist.cons_cons x (List.Sublist.trans h' (List.sublist_append_right stk_rem xs))

private theorem westSortAux_preserves_incSubseq :
    ∀ (xs stk sub : List Nat),
      stk.Pairwise (· ≤ ·) → sub.Pairwise (· < ·) →
      sub.Sublist (stk ++ xs) → sub.Sublist (westSortAux xs stk)
  | [], stk, sub, _, _, hsub => by
    simpa [westSortAux] using hsub
  | x :: rest, stk, sub, hstk, hsub_pw, hsub => by
    rcases westStep_spec stk x hstk with ⟨stk_rem, hsplit, hstk2, _, hrem_ge, _, hstk2_pw⟩
    rw [hsplit, List.append_assoc] at hsub
    rcases sublist_split_append hsub with ⟨s1, s2, heq12, hs1, hs2⟩
    rcases sublist_split_append hs2 with ⟨s_rem, s_tail, heq2, hs_rem, hs_tail⟩
    have hpw2 : s2.Pairwise (· < ·) := by
      have hpw_app := hsub_pw
      rw [heq12] at hpw_app
      exact hpw_app.sublist (List.sublist_append_right s1 s2)
    have hsub2 : s2.Sublist ((westStep stk x).2 ++ rest) := by
      rw [hstk2]
      cases hs_tail with
      | cons _ hs_rest =>
        rw [heq2]
        exact List.Sublist.cons x (List.Sublist.append hs_rem hs_rest)
      | cons_cons _ hs_rest =>
        cases hsr_eq : s_rem with
        | nil =>
          rw [heq2, hsr_eq, List.nil_append]
          exact sublist_cons_cons_of_sublist (.cons_cons x hs_rest)
        | cons u sr =>
          exfalso
          have hu_rem : u ∈ stk_rem := hs_rem.subset (by simp [hsr_eq])
          have hxu : x ≤ u := hrem_ge u hu_rem
          have hp_app := hpw2
          rw [heq2, hsr_eq] at hp_app
          have hlt := (List.pairwise_append.mp hp_app).2.2 u (by simp) x (by simp)
          omega
    have ih := westSortAux_preserves_incSubseq rest (westStep stk x).2 s2 hstk2_pw hpw2 hsub2
    rw [heq12]
    exact List.Sublist.append hs1 ih

/-- **Round-6/8 Theorem 15 (West Stack-Sorting LIS Monotonicity):**
    Every strictly increasing subsequence of `xs : List Nat` remains a subsequence of
    `westSortList xs` (`lis(xs) ≤ lis(S(xs))`). Promotes Round-5 candidate `r5_P_ALL_1lis<=1stack_lis+0`. -/
theorem westSortList_preserves_incSubseq {sub xs : List Nat}
    (h : PermFin.StrictIncSubseq sub xs) :
    PermFin.StrictIncSubseq sub (westSortList xs) :=
  ⟨westSortAux_preserves_incSubseq xs [] sub .nil h.2 (by simpa using h.1), h.2⟩

-- ============================================================================
-- 16. Pop-Stack Sorting Preserves Strictly Increasing Subsequences (`pop_des + lis <= n`)
-- ============================================================================

private theorem flatMap_reverse_preserves_incSubseq :
    ∀ (L : List (List Nat)) (sub : List Nat),
      (∀ r ∈ L, r.Pairwise (· > ·)) → sub.Pairwise (· < ·) →
      sub.Sublist (concatRuns L) → sub.Sublist (L.flatMap List.reverse)
  | [], sub, _, _, hsub => by
    simpa [concatRuns] using hsub
  | r :: rs, sub, hL, hpw, hsub => by
    simp only [concatRuns] at hsub
    rcases sublist_split_append hsub with ⟨s1, s2, heq, hs1, hs2⟩
    have hpw1 : s1.Pairwise (· < ·) := by
      have hp := hpw
      rw [heq] at hp
      exact hp.sublist (List.sublist_append_left s1 s2)
    have hpw2 : s2.Pairwise (· < ·) := by
      have hp := hpw
      rw [heq] at hp
      exact hp.sublist (List.sublist_append_right s1 s2)
    have hr_gt : r.Pairwise (· > ·) := hL r (by simp)
    have hs1_gt : s1.Pairwise (· > ·) := hr_gt.sublist hs1
    have hs1_rev : s1.Sublist r.reverse := by
      cases hs1_eq : s1 with
      | nil => exact List.nil_sublist _
      | cons a s1_tail =>
        cases s1_tail with
        | nil =>
          have ha : a ∈ r := hs1.subset (by simp [hs1_eq])
          exact List.singleton_sublist.mpr (List.mem_reverse.mpr ha)
        | cons b _ =>
          rw [hs1_eq] at hpw1 hs1_gt
          have hlt : a < b := (List.pairwise_cons.mp hpw1).1 b (by simp)
          have hgt : a > b := (List.pairwise_cons.mp hs1_gt).1 b (by simp)
          omega
    have ih := flatMap_reverse_preserves_incSubseq rs s2 (fun u hu => hL u (by simp [hu])) hpw2 hs2
    rw [heq, List.flatMap_cons]
    exact List.Sublist.append hs1_rev ih

/-- **Round-9 Theorem 16a (Pop-Stack Sorting LIS Preservation):**
    Reversing each strictly decreasing run preserves every strictly increasing subsequence. -/
theorem popSortList_preserves_incSubseq {sub xs : List Nat}
    (h : PermFin.StrictIncSubseq sub xs) :
    PermFin.StrictIncSubseq sub (popSortList xs) := by
  refine ⟨flatMap_reverse_preserves_incSubseq (popRuns xs) sub ?_ h.2 ?_, h.2⟩
  · intro r hr
    exact (popRuns_nonempty_and_pairwise xs r hr).2
  · rw [concatRuns_popRuns xs]
    exact h.1

private theorem flatMap_reverse_length (L : List (List Nat)) :
    (L.flatMap List.reverse).length = (concatRuns L).length := by
  induction L with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.flatMap_cons, concatRuns, List.length_append, List.length_reverse, ih]

/-- **Round-9 Theorem 16b (`pop_des + lis ≤ n`):**
    Every permutation `p : PermFin n` and strictly increasing subsequence `sub` of `p.toList`
    satisfies `p.popDes + sub.length ≤ n`. Proved universally over all `n : Nat`. -/
theorem PermFin.popDes_add_incSubseq_le {n : Nat} (p : PermFin n) (sub : List Nat)
    (hinc : PermFin.StrictIncSubseq sub p.toList) :
    p.popDes + sub.length ≤ n := by
  have hinc' := popSortList_preserves_incSubseq hinc
  have hle := des_add_incSubseq_le_length (popSortList p.toList) sub hinc'.1 hinc'.2
  have hlen : (popSortList p.toList).length = n := by
    unfold popSortList
    rw [flatMap_reverse_length, concatRuns_popRuns, PermFin.toList]
    simp
  unfold PermFin.popDes
  omega

-- ============================================================================
-- 17. Connected Graph Diameter Bounded by Induced P4 Count + 2 (`diam <= ind_p4 + 2`)
-- ============================================================================

private theorem one_le_countP_of_mem {α : Type} (xs : List α) (p : α → Bool)
    {b : α} (hb : b ∈ xs) (hp : p b = true) :
    1 ≤ xs.countP p := by
  rw [countP_eq_sumNat]
  apply one_le_sumNat_of_exists
  exact ⟨b, hb, by simp [hp]⟩

private theorem ordEdge_fst_mem {n : Nat} (a b : Fin n) :
    a = (SimpleGraphFin.ordEdge a b).1 ∨ a = (SimpleGraphFin.ordEdge a b).2 := by
  dsimp [SimpleGraphFin.ordEdge]
  split
  · left; rfl
  · right; rfl

private theorem ordEdge_snd_mem {n : Nat} (a b : Fin n) :
    b = (SimpleGraphFin.ordEdge a b).1 ∨ b = (SimpleGraphFin.ordEdge a b).2 := by
  dsimp [SimpleGraphFin.ordEdge]
  split
  · right; rfl
  · left; rfl

/-- **Round-9 Theorem 17 (`diam ≤ ind_p4 + 2`):**
    In every finite connected graph `G`, every pair of vertices separated by geodesic distance
    `d ≥ 3` provides `d - 2` distinct induced `P_4` central edges along the geodesic. -/
theorem SimpleGraphFin.connected_diam_le_indP4_add_two {n d : Nat}
    (G : SimpleGraphFin n) (hd : G.DiameterNum d) :
    d ≤ G.indP4Cnt + 2 := by
  by_cases hd2 : d ≤ 2
  · omega
  · have hdpos : 1 ≤ d := by omega
    rcases diameterNum_geodesic G hd hdpos with ⟨u0, v0, W, hne, hhead, hlast, hw, hlen, hno⟩
    let mkMid : Nat → Fin n × Fin n := fun i =>
      SimpleGraphFin.ordEdge (nthOr W (i + 1) u0) (nthOr W (i + 2) u0)
    let p4Edge : Fin n → Fin n → Nat := fun u v =>
      if decide (u.val < v.val) && G.adj u v then
        sumNat (List.finRange n) (fun a =>
          if G.adj u a && !(G.adj v a) && decide (a ≠ v) then
            (List.finRange n).countP (fun b =>
              G.adj v b && !(G.adj u b) && decide (b ≠ u) && !(G.adj a b))
          else 0)
      else 0
    have hind_eq : G.indP4Cnt =
        sumNat (List.finRange n) (fun u => sumNat (List.finRange n) (fun v => p4Edge u v)) :=
      rfl
    let ind : Nat → Fin n → Fin n → Nat := fun i u v =>
      if decide (mkMid i = (u, v)) then 1 else 0
    have hconst : sumNat (List.range (d - 2)) (fun _ => 1) = d - 2 := by
      have := sumNat_const (List.range (d - 2)) 1
      simpa using this
    have hlow : d - 2 ≤
        sumNat (List.range (d - 2)) (fun i =>
          sumNat (List.finRange n) (fun u =>
            sumNat (List.finRange n) (fun v => ind i u v))) := by
      calc d - 2 = sumNat (List.range (d - 2)) (fun _ => 1) := hconst.symm
        _ ≤ _ := by
          apply sumNat_mono
          intro i _
          apply one_le_sumNat_of_exists
          refine ⟨(mkMid i).1, List.mem_finRange _, ?_⟩
          apply one_le_sumNat_of_exists
          refine ⟨(mkMid i).2, List.mem_finRange _, ?_⟩
          simp [ind]
    have hswap1 :
        sumNat (List.range (d - 2)) (fun i =>
          sumNat (List.finRange n) (fun u =>
            sumNat (List.finRange n) (fun v => ind i u v))) =
        sumNat (List.finRange n) (fun u =>
          sumNat (List.range (d - 2)) (fun i =>
            sumNat (List.finRange n) (fun v => ind i u v))) :=
      sumNat_swap (List.range (d - 2)) (List.finRange n)
        (fun i u => sumNat (List.finRange n) (fun v => ind i u v))
    have hswap2 : ∀ u : Fin n,
        sumNat (List.range (d - 2)) (fun i =>
          sumNat (List.finRange n) (fun v => ind i u v)) =
        sumNat (List.finRange n) (fun v =>
          sumNat (List.range (d - 2)) (fun i => ind i u v)) := fun u =>
      sumNat_swap (List.range (d - 2)) (List.finRange n) (fun i v => ind i u v)
    have hcell : ∀ u v : Fin n,
        sumNat (List.range (d - 2)) (fun i => ind i u v) ≤ p4Edge u v := by
      intro u v
      let q : Nat → Bool := fun i => decide (mkMid i = (u, v))
      cases hmin : minTrue? q (d - 2) with
      | none =>
        have hz := sumNat_range_eq_zero_of_all_false q (d - 2) (minTrue?_eq_none q (d - 2) hmin)
        have hind0 : sumNat (List.range (d - 2)) (fun i => ind i u v) = 0 := by
          simpa [ind, q] using hz
        rw [hind0]
        exact Nat.zero_le _
      | some i0 =>
        have ⟨hi0_lt, hi0_t, hi0_min⟩ := minTrue?_eq_some q (d - 2) i0 hmin
        have huniq : ∀ j : Nat, j < d - 2 → q j = true → j = i0 := by
          intro j hj_lt hqt
          by_cases hji : j < i0
          · have hf := hi0_min j hji
            rw [hqt] at hf; cases hf
          · by_cases hij : i0 < j
            · exfalso
              have heq_i : mkMid i0 = (u, v) := of_decide_eq_true hi0_t
              have heq_j : mkMid j = (u, v) := of_decide_eq_true hqt
              have heq : mkMid i0 = mkMid j := heq_i.trans heq_j.symm
              have hmem1 := ordEdge_fst_mem (nthOr W (i0 + 1) u0) (nthOr W (i0 + 2) u0)
              dsimp only [mkMid] at heq
              rw [heq] at hmem1
              rcases hmem1 with hm | hm
              · have hmem2 := ordEdge_mem (Or.inl hm)
                rcases hmem2 with h1 | h2
                · exact geodesic_no_repeat G W hne hhead hlast hw hlen hno (i0 + 1) (j + 1) (by omega) (by omega) h1
                · exact geodesic_no_repeat G W hne hhead hlast hw hlen hno (i0 + 1) (j + 2) (by omega) (by omega) h2
              · have hmem2 := ordEdge_mem (Or.inr hm)
                rcases hmem2 with h1 | h2
                · exact geodesic_no_repeat G W hne hhead hlast hw hlen hno (i0 + 1) (j + 1) (by omega) (by omega) h1
                · exact geodesic_no_repeat G W hne hhead hlast hw hlen hno (i0 + 1) (j + 2) (by omega) (by omega) h2
            · omega
        have hle1 : sumNat (List.range (d - 2)) (fun i => ind i u v) ≤ 1 := by
          have hm : sumNat (List.range (d - 2)) (fun i => ind i u v) ≤
              sumNat (List.range (d - 2)) (fun i => if decide (i = i0) then 1 else 0) := by
            apply sumNat_mono
            intro j hj
            have hjm : j < d - 2 := List.mem_range.mp hj
            simp only [ind]
            cases hqj : q j with
            | false =>
              have hne_eq : mkMid j ≠ (u, v) := by
                intro heq; simp [q, heq] at hqj
              simp [hne_eq]
            | true =>
              have hji0 : j = i0 := huniq j hjm hqj
              simp [hji0]
              split <;> omega
          exact Nat.le_trans hm (sumNat_range_decide_eq_le_one (d - 2) i0)
        have heq_uv : mkMid i0 = (u, v) := of_decide_eq_true hi0_t
        let x0 := nthOr W i0 u0
        let x1 := nthOr W (i0 + 1) u0
        let x2 := nthOr W (i0 + 2) u0
        let x3 := nthOr W (i0 + 3) u0
        have hx01 : G.adj x0 x1 = true := isWalk_nthOr_adj G u0 W hw i0 (by omega)
        have hx12 : G.adj x1 x2 = true := isWalk_nthOr_adj G u0 W hw (i0 + 1) (by omega)
        have hx23 : G.adj x2 x3 = true := isWalk_nthOr_adj G u0 W hw (i0 + 2) (by omega)
        have hna02 : G.adj x0 x2 = false := geodesic_no_shortcut G W hne hhead hlast hw hlen hno i0 (i0 + 2) (by omega) (by omega)
        have hna13 : G.adj x1 x3 = false := geodesic_no_shortcut G W hne hhead hlast hw hlen hno (i0 + 1) (i0 + 3) (by omega) (by omega)
        have hna03 : G.adj x0 x3 = false := geodesic_no_shortcut G W hne hhead hlast hw hlen hno i0 (i0 + 3) (by omega) (by omega)
        have hne12 : x1 ≠ x2 := geodesic_no_repeat G W hne hhead hlast hw hlen hno (i0 + 1) (i0 + 2) (by omega) (by omega)
        have hne02 : x0 ≠ x2 := geodesic_no_repeat G W hne hhead hlast hw hlen hno i0 (i0 + 2) (by omega) (by omega)
        have hne13 : x1 ≠ x3 := geodesic_no_repeat G W hne hhead hlast hw hlen hno (i0 + 1) (i0 + 3) (by omega) (by omega)
        have hp4_ge1 : 1 ≤ p4Edge u v := by
          dsimp only [mkMid, SimpleGraphFin.ordEdge] at heq_uv
          by_cases hlt : x1.val < x2.val
          · have huv : (x1, x2) = (u, v) := by simpa [x1, x2, hlt] using heq_uv
            have hu : u = x1 := (Prod.ext_iff.mp huv).1.symm
            have hv : v = x2 := (Prod.ext_iff.mp huv).2.symm
            subst hu; subst hv
            have hcond : (decide (x1.val < x2.val) && G.adj x1 x2) = true := by
              simp [hlt, hx12]
            dsimp only [p4Edge]
            simp only [hcond, ↓reduceIte]
            apply one_le_sumNat_of_exists
            refine ⟨x0, List.mem_finRange _, ?_⟩
            have hx10 : G.adj x1 x0 = true := by rw [G.symm]; exact hx01
            have hx20 : G.adj x2 x0 = false := by rw [G.symm]; exact hna02
            have ha_ok : (G.adj x1 x0 && !(G.adj x2 x0) && decide (x0 ≠ x2)) = true := by
              simp [hx10, hx20, hne02]
            simp only [ha_ok, ↓reduceIte]
            apply one_le_countP_of_mem (List.finRange n) _ (List.mem_finRange x3)
            have hne31 : x3 ≠ x1 := hne13.symm
            simp [hx23, hna13, hne31, hna03]
          · have hrev : x2.val < x1.val := by
              have hvne : x1.val ≠ x2.val := fun h => hne12 (Fin.ext h)
              omega
            have huv : (x2, x1) = (u, v) := by simpa [x1, x2, hlt] using heq_uv
            have hu : u = x2 := (Prod.ext_iff.mp huv).1.symm
            have hv : v = x1 := (Prod.ext_iff.mp huv).2.symm
            subst hu; subst hv
            have hx21 : G.adj x2 x1 = true := by rw [G.symm]; exact hx12
            have hcond : (decide (x2.val < x1.val) && G.adj x2 x1) = true := by
              simp [hrev, hx21]
            dsimp only [p4Edge]
            simp only [hcond, ↓reduceIte]
            apply one_le_sumNat_of_exists
            refine ⟨x3, List.mem_finRange _, ?_⟩
            have hne31 : x3 ≠ x1 := hne13.symm
            have hx31 : G.adj x1 x3 = false := hna13
            have ha_ok : (G.adj x2 x3 && !(G.adj x1 x3) && decide (x3 ≠ x1)) = true := by
              simp [hx23, hx31, hne31]
            simp only [ha_ok, ↓reduceIte]
            apply one_le_countP_of_mem (List.finRange n) _ (List.mem_finRange x0)
            have hx10 : G.adj x1 x0 = true := by rw [G.symm]; exact hx01
            have hx20 : G.adj x2 x0 = false := by rw [G.symm]; exact hna02
            have hx30 : G.adj x3 x0 = false := by rw [G.symm]; exact hna03
            simp [hx10, hx20, hne02, hx30]
        omega
    have htot :
        sumNat (List.finRange n) (fun u =>
          sumNat (List.finRange n) (fun v => sumNat (List.range (d - 2)) (fun i => ind i u v))) ≤
        G.indP4Cnt := by
      rw [hind_eq]
      apply sumNat_mono
      intro u _
      apply sumNat_mono
      intro v _
      exact hcell u v
    have hswap2_sum :
        sumNat (List.finRange n) (fun u =>
          sumNat (List.range (d - 2)) (fun i => sumNat (List.finRange n) (fun v => ind i u v))) =
        sumNat (List.finRange n) (fun u =>
          sumNat (List.finRange n) (fun v => sumNat (List.range (d - 2)) (fun i => ind i u v))) := by
      apply sumNat_congr
      intro u _
      exact hswap2 u
    omega

-- ============================================================================
-- 18. Additive Set Cardinality + Symmetry Defect Bound (`2*k + sym_defect <= diffset + 1`)
-- ============================================================================

private theorem sumNat_range_add (a b : Nat) (f : Nat → Nat) :
    sumNat (List.range (a + b)) f =
      sumNat (List.range a) f + sumNat (List.range b) (fun k => f (a + k)) := by
  induction b with
  | zero => simp [sumNat]
  | succ b ih =>
    rw [← Nat.add_assoc, List.range_succ, sumNat_append, ih, List.range_succ, sumNat_append]
    simp only [sumNat]
    omega

private theorem range_mem_any_pair (N a b : Nat) (ha : a < N) (hb : b < N)
    (P : Nat → Nat → Bool) (hp : P a b = true) :
    ((List.range N).any (fun x => (List.range N).any (fun y => P x y))) = true := by
  rw [List.any_eq_true]
  refine ⟨a, List.mem_range.mpr ha, ?_⟩
  rw [List.any_eq_true]
  exact ⟨b, List.mem_range.mpr hb, hp⟩

/-- **Round-9 Theorem 18 (`2 * k + sym_defect ≤ diffset + 1`):**
    Every normalized additive subset `A ⊆ {0, ..., N-1}` (`0, N-1 ∈ A`) satisfies
    `2 * |A| + sym_defect(A) ≤ |A - A| + 1`, proved universally over all `N ≥ 1`. -/
theorem two_card_add_symDefect_le_diffset_add_one (A : Nat → Bool) (N : Nat)
    (hN : 1 ≤ N) (h0 : A 0 = true) (hmax : A (N - 1) = true) :
    2 * cardPrefix A N + symDefectPrefix A N ≤ intDiffsetCard A N + 1 := by
  let m := N - 1
  have hmN : N = m + 1 := by omega
  have hm_true : A m = true := hmax
  let isDiff : Nat → Bool := fun s =>
    (List.range (m + 1)).any (fun a =>
      (List.range (m + 1)).any (fun b =>
        A a && A b && decide (a + m = s + b)))
  let f : Nat → Nat := fun s => if isDiff s then 1 else 0
  have hdiff_eq : intDiffsetCard A N = sumNat (List.range (2 * (m + 1))) f := by
    unfold intDiffsetCard
    rw [hmN, countP_eq_sumNat]
    rfl
  have h2m : 2 * (m + 1) = m + (m + 2) := by omega
  have hsplit_all :
      intDiffsetCard A N = sumNat (List.range m) f + sumNat (List.range (m + 2)) (fun k => f (m + k)) := by
    rw [hdiff_eq, h2m, sumNat_range_add]
  have hfm_le1 : f m ≤ 1 := by
    dsimp [f]
    split <;> omega
  have hrange_m1 : sumNat (List.range (m + 1)) f = sumNat (List.range m) f + f m := by
    rw [List.range_succ, sumNat_append]
    simp [sumNat]
  have hrange_pos :
      sumNat (List.range (m + 1)) (fun k => f (m + k)) ≤
        sumNat (List.range (m + 2)) (fun k => f (m + k)) := by
    have h2_succ : List.range (m + 2) = List.range (m + 1) ++ [m + 1] := List.range_succ
    rw [h2_succ, sumNat_append]
    omega
  have hdiff_upper :
      sumNat (List.range (m + 1)) f + sumNat (List.range (m + 1)) (fun k => f (m + k)) ≤
        intDiffsetCard A N + 1 := by
    omega
  have hrev_f : sumNat (List.range (m + 1)) f = sumNat (List.range (m + 1)) (fun x => f (m - x)) :=
    (sumNat_range_rev m f).symm
  have hpoint : ∀ x ∈ List.range (m + 1),
      (if A x then 1 else 0) + (if A (m - x) then 1 else 0) +
        (if A x != A (m - x) then 1 else 0) ≤ f (m - x) + f (m + x) := by
    intro x hx
    have hxm : x ≤ m := Nat.lt_succ_iff.mp (List.mem_range.mp hx)
    have hx_diff : A x = true → isDiff (m + x) = true ∧ isDiff (m - x) = true := by
      intro hax
      constructor
      · refine range_mem_any_pair (m + 1) x 0 (by omega) (by omega) _ ?_
        simp [hax, h0, Nat.add_comm]
      · refine range_mem_any_pair (m + 1) 0 x (by omega) (by omega) _ ?_
        have hsum0 : 0 + m = (m - x) + x := by omega
        simp [h0, hax, hsum0]
    have hmx_diff : A (m - x) = true → isDiff (m + x) = true ∧ isDiff (m - x) = true := by
      intro hamx
      constructor
      · refine range_mem_any_pair (m + 1) m (m - x) (by omega) (by omega) _ ?_
        have hsumm : m + m = (m + x) + (m - x) := by omega
        simp [hm_true, hamx, hsumm]
      · refine range_mem_any_pair (m + 1) (m - x) m (by omega) (by omega) _ ?_
        simp [hamx, hm_true]
    cases hax : A x <;> cases hamx : A (m - x)
    · simp
    · obtain ⟨hp, hn⟩ := hmx_diff hamx
      simp [f, hp, hn]
    · obtain ⟨hp, hn⟩ := hx_diff hax
      simp [f, hp, hn]
    · obtain ⟨hp, hn⟩ := hx_diff hax
      simp [f, hp, hn]
  have hsum_point := sumNat_mono (List.range (m + 1)) _ _ hpoint
  rw [sumNat_add, sumNat_add, sumNat_add] at hsum_point
  have hcard1 : sumNat (List.range (m + 1)) (fun x => if A x then 1 else 0) = cardPrefix A N := by
    rw [hmN]; rfl
  have hcard2 : sumNat (List.range (m + 1)) (fun x => if A (m - x) then 1 else 0) = cardPrefix A N := by
    rw [hmN, sumNat_range_rev m (fun x => if A x then 1 else 0)]
    rfl
  have hsym : sumNat (List.range (m + 1)) (fun x => if A x != A (m - x) then 1 else 0) =
      symDefectPrefix A N := by
    unfold symDefectPrefix
    rw [hmN]
    apply sumNat_congr
    intro x _
    have hnm : m + 1 - 1 - x = m - x := by omega
    rw [hnm]
  omega

-- ============================================================================
-- 19. Solution to `Conj_AllPerms_StackInv_Le_PopInv` (`inv(S(p)) <= inv(P(p))`)
-- ============================================================================

private theorem r10_westStep_spec (stk : List Nat) (x : Nat) (hstk : stk.Pairwise (· ≤ ·)) :
    ∃ stk_rem,
      stk = (westStep stk x).1 ++ stk_rem ∧
      (westStep stk x).2 = x :: stk_rem ∧
      (∀ s ∈ (westStep stk x).1, s < x) ∧
      (∀ u ∈ stk_rem, x ≤ u) ∧
      (westStep stk x).1.Pairwise (· ≤ ·) ∧
      (westStep stk x).2.Pairwise (· ≤ ·) := by
  induction stk with
  | nil =>
    refine ⟨[], rfl, rfl, fun _ h => by simp [westStep] at h, fun _ h => by simp at h, ?_, ?_⟩
    · simp [westStep]
    · simp only [westStep]
      exact .cons (fun _ h => by simp at h) .nil
  | cons top rest ih =>
    cases hstk with
    | cons htop hrest =>
      by_cases hlt : top < x
      · rcases ih hrest with ⟨stk_rem, hsplit, hstk2, hpop, hrem, hpw_pop, hpw_stk2⟩
        have hstep : westStep (top :: rest) x = (top :: (westStep rest x).1, (westStep rest x).2) := by
          simp [westStep, hlt]
        refine ⟨stk_rem, ?_, ?_, ?_, hrem, ?_, ?_⟩
        · rw [hstep]; simp only [List.cons_append]; rw [← hsplit]
        · rw [hstep]; exact hstk2
        · intro s hs
          rw [hstep] at hs
          rcases List.mem_cons.mp hs with rfl | hs'
          · exact hlt
          · exact hpop s hs'
        · rw [hstep]
          refine .cons (fun z hz => htop z ?_) hpw_pop
          rw [hsplit]
          exact List.mem_append_left stk_rem hz
        · rw [hstep]; exact hpw_stk2
      · have hle : x ≤ top := by omega
        have hstep : westStep (top :: rest) x = ([], x :: top :: rest) := by
          simp [westStep, hlt]
        refine ⟨top :: rest, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hstep]; rfl
        · rw [hstep]
        · intro _ h; rw [hstep] at h; simp at h
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu'
          · exact hle
          · exact Nat.le_trans hle (htop u hu')
        · rw [hstep]; exact .nil
        · rw [hstep]
          refine .cons (fun u hu => ?_) (.cons htop hrest)
          rcases List.mem_cons.mp hu with rfl | hu'
          · exact hle
          · exact Nat.le_trans hle (htop u hu')

private theorem r10_westSortAux_countP (P : Nat → Bool) (xs stk : List Nat) :
    (westSortAux xs stk).countP P = stk.countP P + xs.countP P := by
  induction xs generalizing stk with
  | nil => simp [westSortAux]
  | cons x xs ih =>
    unfold westSortAux
    have hstep_sum : ∀ s : List Nat, (westStep s x).1.countP P + (westStep s x).2.countP P =
        s.countP P + (if P x then 1 else 0) := by
      intro s
      induction s with
      | nil =>
        simp only [westStep, List.countP_nil, List.countP_cons]
        cases P x <;> simp <;> omega
      | cons t ts ihs =>
        by_cases hlt : t < x
        · have hs : westStep (t :: ts) x = (t :: (westStep ts x).1, (westStep ts x).2) := by
            simp [westStep, hlt]
          rw [hs, List.countP_cons, List.countP_cons]
          have _ := ihs
          cases P t <;> simp <;> omega
        · have hs : westStep (t :: ts) x = ([], x :: t :: ts) := by
            simp [westStep, hlt]
          rw [hs, List.countP_nil, List.countP_cons, List.countP_cons]
          cases P x <;> cases P t <;> simp <;> omega
    rw [List.countP_append, ih, List.countP_cons, ← Nat.add_assoc, hstep_sum stk]
    omega

private theorem r10_countP_zero_of_forall {α : Type} (xs : List α) (P : α → Bool)
    (h : ∀ x ∈ xs, P x = false) : xs.countP P = 0 := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    rw [List.countP_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    rfl

private theorem r10_inv_zero_of_pw {xs : List Nat} (hpw : xs.Pairwise (· ≤ ·)) :
    listInvCnt xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases hpw with
    | cons hx hrest =>
      unfold listInvCnt
      have h0 : rest.countP (fun b => decide (b < x)) = 0 :=
        r10_countP_zero_of_forall rest _ (fun b hb => decide_eq_false (by have := hx b hb; omega))
      rw [h0, ih hrest]

private theorem r10_inv_append (ys zs : List Nat) :
    listInvCnt (ys ++ zs) =
      listInvCnt ys + sumNat ys (fun a => zs.countP (fun b => decide (b < a))) + listInvCnt zs := by
  induction ys with
  | nil => simp [listInvCnt, sumNat]
  | cons a yr ih =>
    simp only [List.cons_append, listInvCnt, sumNat, List.countP_append, ih]
    omega

private theorem r10_rev_pw_le_of_gt {xs : List Nat} (hpw : xs.Pairwise (· > ·)) :
    xs.reverse.Pairwise (· ≤ ·) := by
  rw [List.pairwise_reverse]
  exact hpw.imp (fun h => Nat.le_of_lt h)

private theorem r10_sumNat_reverse {α : Type} (xs : List α) (f : α → Nat) :
    sumNat xs.reverse f = sumNat xs f := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.reverse_cons, sumNat_append, sumNat, ih]
    omega

private def r10_concatRuns : List (List Nat) → List Nat
  | [] => []
  | r :: rs => r ++ r10_concatRuns rs

private theorem r10_flatMap_rev_countP (P : Nat → Bool) (L : List (List Nat)) :
    (L.flatMap List.reverse).countP P = (r10_concatRuns L).countP P := by
  induction L with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.flatMap_cons, r10_concatRuns, List.countP_append, List.countP_reverse, ih]

private theorem r10_concatRuns_popRuns (xs : List Nat) :
    r10_concatRuns (popRuns xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases hpr : popRuns rest with
    | nil =>
      rw [hpr, r10_concatRuns] at ih
      subst ih
      simp [popRuns, r10_concatRuns]
    | cons r0 rs =>
      cases r0 with
      | nil =>
        simp only [popRuns, hpr, r10_concatRuns]
        simpa [hpr, r10_concatRuns] using ih
      | cons y ys =>
        simp only [popRuns, hpr]
        by_cases hlt : y < x
        · simp only [hlt, ↓reduceIte, r10_concatRuns, List.cons_append]
          simpa [hpr, r10_concatRuns] using ih
        · simp only [hlt, ↓reduceIte, r10_concatRuns, List.singleton_append]
          simpa [hpr, r10_concatRuns] using ih

private theorem r10_popRuns_spec (xs : List Nat) :
    ∀ r ∈ popRuns xs, r ≠ [] ∧ r.Pairwise (· > ·) := by
  induction xs with
  | nil => intro _ h; simp [popRuns] at h
  | cons x rest ih =>
    cases hpr : popRuns rest with
    | nil =>
      intro r hr
      simp [popRuns, hpr] at hr
      subst hr
      exact ⟨by simp, List.pairwise_singleton _ _⟩
    | cons r0 rs =>
      cases r0 with
      | nil =>
        exfalso
        exact (ih [] (by rw [hpr]; simp)).1 rfl
      | cons y ys =>
        have hy_pw := (ih (y :: ys) (by rw [hpr]; simp)).2
        simp only [popRuns, hpr]
        by_cases hlt : y < x
        · simp only [hlt, ↓reduceIte]
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hrs
          · refine ⟨by simp, .cons (fun z hz => ?_) hy_pw⟩
            rcases List.mem_cons.mp hz with rfl | hzs
            · exact hlt
            · have hyz := (List.pairwise_cons.mp hy_pw).1 z hzs
              omega
          · exact ih r (by rw [hpr]; simp [hrs])
        · simp only [hlt, ↓reduceIte]
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr'
          · exact ⟨by simp, List.pairwise_singleton _ _⟩
          · exact ih r (by rw [hpr]; exact hr')

private theorem r10_westSortAux_dec_run :
    ∀ (t ys stk : List Nat) (u : Nat),
      (u :: t).Pairwise (· > ·) →
      westSortAux (t ++ ys) (u :: stk) = westSortAux ys (t.reverse ++ (u :: stk))
  | [], _, _, _, _ => by simp
  | y :: tr, ys, stk, u, hpw => by
    have huy : y < u := (List.pairwise_cons.mp hpw).1 y (by simp)
    have hnot : ¬ (u < y) := by omega
    have hstep : westStep (u :: stk) y = ([], y :: u :: stk) := by simp [westStep, hnot]
    have ih := r10_westSortAux_dec_run tr ys (u :: stk) y (List.pairwise_cons.mp hpw).2
    simp only [List.cons_append, westSortAux, hstep, List.nil_append]
    rw [ih, List.reverse_cons, List.append_assoc]
    rfl

private theorem r10_westSortAux_runs_inv_le :
    ∀ (L : List (List Nat)) (stk : List Nat),
      (∀ r ∈ L, r ≠ [] ∧ r.Pairwise (· > ·)) →
      stk.Pairwise (· ≤ ·) →
      listInvCnt (westSortAux (r10_concatRuns L) stk) ≤
        sumNat stk (fun s => (r10_concatRuns L).countP (fun b => decide (b < s))) +
        listInvCnt (L.flatMap List.reverse)
  | [], stk, _, hstk => by
    simp [r10_concatRuns, westSortAux, r10_inv_zero_of_pw hstk]
  | r :: rs, stk, hL, hstk => by
    obtain ⟨hr_ne, hr_pw⟩ := hL r (by simp)
    cases r with
    | nil => exact absurd rfl hr_ne
    | cons x rt =>
      let ys := r10_concatRuns rs
      rcases r10_westStep_spec stk x hstk with ⟨stk_rem, hsplit, hstk2, hpop_lt, hrem_ge, hpop_pw, hstk2_pw⟩
      have hrem_pw : stk_rem.Pairwise (· ≤ ·) := (List.pairwise_cons.mp (hstk2 ▸ hstk2_pw)).2
      have hrun_step :
          westSortAux (r10_concatRuns ((x :: rt) :: rs)) stk =
          (westStep stk x).1 ++ westSortAux ys ((x :: rt).reverse ++ stk_rem) := by
        change (westStep stk x).1 ++ westSortAux (rt ++ ys) (westStep stk x).2 = _
        rw [hstk2, r10_westSortAux_dec_run rt ys stk_rem x hr_pw, List.reverse_cons, List.append_assoc]
        rfl
      have hstk'_pw : ((x :: rt).reverse ++ stk_rem).Pairwise (· ≤ ·) := by
        rw [List.pairwise_append]
        refine ⟨r10_rev_pw_le_of_gt hr_pw, hrem_pw, ?_⟩
        intro a ha z hz
        have hxz : x ≤ z := hrem_ge z hz
        rw [List.mem_reverse] at ha
        rcases List.mem_cons.mp ha with rfl | hart
        · exact hxz
        · have hax : a < x := (List.pairwise_cons.mp hr_pw).1 a hart
          omega
      have ih := r10_westSortAux_runs_inv_le rs ((x :: rt).reverse ++ stk_rem)
        (fun s hs => hL s (by simp [hs])) hstk'_pw
      change listInvCnt (westSortAux ys ((x :: rt).reverse ++ stk_rem)) ≤
        sumNat ((x :: rt).reverse ++ stk_rem) (fun s => ys.countP (fun b => decide (b < s))) +
        listInvCnt (rs.flatMap List.reverse) at ih
      rw [sumNat_append, r10_sumNat_reverse] at ih
      have hpop_cross :
          sumNat (westStep stk x).1 (fun p =>
            (westSortAux ys ((x :: rt).reverse ++ stk_rem)).countP (fun b => decide (b < p))) =
          sumNat (westStep stk x).1 (fun p =>
            ((x :: rt) ++ ys).countP (fun b => decide (b < p))) := by
        apply sumNat_congr
        intro p hp
        have hpx : p < x := hpop_lt p hp
        rw [r10_westSortAux_countP, List.countP_append, List.countP_append, List.countP_reverse]
        have hrem0 : stk_rem.countP (fun b => decide (b < p)) = 0 :=
          r10_countP_zero_of_forall stk_rem _ (fun z hz => decide_eq_false (by have := hrem_ge z hz; omega))
        rw [hrem0]
        omega
      have hrem_mono :
          sumNat stk_rem (fun s => ys.countP (fun b => decide (b < s))) ≤
          sumNat stk_rem (fun s => ((x :: rt) ++ ys).countP (fun b => decide (b < s))) := by
        apply sumNat_mono
        intro s _
        rw [List.countP_append]
        omega
      have hstk_sum :
          sumNat stk (fun s => (r10_concatRuns ((x :: rt) :: rs)).countP (fun b => decide (b < s))) =
          sumNat (westStep stk x).1 (fun s => ((x :: rt) ++ ys).countP (fun b => decide (b < s))) +
          sumNat stk_rem (fun s => ((x :: rt) ++ ys).countP (fun b => decide (b < s))) := by
        change sumNat stk (fun s => ((x :: rt) ++ ys).countP (fun b => decide (b < s))) = _
        conv => lhs; rw [hsplit]
        exact sumNat_append _ _ _
      have hrhs_inv :
          listInvCnt (((x :: rt) :: rs).flatMap List.reverse) =
          sumNat (x :: rt) (fun a => ys.countP (fun b => decide (b < a))) +
          listInvCnt (rs.flatMap List.reverse) := by
        simp only [List.flatMap_cons]
        rw [r10_inv_append, r10_inv_zero_of_pw (r10_rev_pw_le_of_gt hr_pw), r10_sumNat_reverse]
        have hcr :
            sumNat (x :: rt) (fun a => (rs.flatMap List.reverse).countP (fun b => decide (b < a))) =
            sumNat (x :: rt) (fun a => ys.countP (fun b => decide (b < a))) := by
          apply sumNat_congr
          intro a _
          exact r10_flatMap_rev_countP _ rs
        rw [hcr]
        omega
      rw [hrun_step, r10_inv_append, r10_inv_zero_of_pw hpop_pw, hpop_cross, hstk_sum, hrhs_inv]
      omega

/-- **Round-10 Theorem 19a (West Stack Sort vs. Pop-Stack Sort Inversions on Arbitrary Lists):**
    For every list `xs : List Nat`, one pass of West's stack-sorting map leaves no more inversions
    than one pass of pop-stack sorting (`listInvCnt (westSortList xs) ≤ listInvCnt (popSortList xs)`). -/
theorem westSortList_inv_le_popSortList_inv (xs : List Nat) :
    listInvCnt (westSortList xs) ≤ listInvCnt (popSortList xs) := by
  have h := r10_westSortAux_runs_inv_le (popRuns xs) [] (r10_popRuns_spec xs) .nil
  rw [r10_concatRuns_popRuns xs] at h
  simpa [westSortList, popSortList, sumNat] using h

/-- **Round-10 Theorem 19b (Solution to `Conj_AllPerms_StackInv_Le_PopInv`):**
    Every permutation `p : PermFin n` satisfies `p.stackInv ≤ p.popInv`, proved universally
    over all `n : Nat`. -/
theorem PermFin.stackInv_le_popInv {n : Nat} (p : PermFin n) :
    p.stackInv ≤ p.popInv :=
  westSortList_inv_le_popSortList_inv p.toList

-- ============================================================================
-- 20. Solution to `Conj_Av321_TwoStackInv_Pat231` (`3 * inv(S^2(p)) <= pat231(p)` on `Av(321)`)
-- ============================================================================

private def r10_beforeGt : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, v =>
    if x = v then 0
    else (if v < x then 1 else 0) + r10_beforeGt xs v

private theorem r10_beforeGt_append_not_mem (ys zs : List Nat) (v : Nat) (hnot : v ∉ ys) :
    r10_beforeGt (ys ++ zs) v = ys.countP (fun x => decide (v < x)) + r10_beforeGt zs v := by
  induction ys with
  | nil => simp
  | cons y yr ih =>
    have hyv : y ≠ v := fun h => hnot (by simp [h])
    have ihr := ih (fun hm => hnot (by simp [hm]))
    simp only [List.cons_append, r10_beforeGt, hyv, ↓reduceIte, List.countP_cons, ihr]
    by_cases hlt : v < y <;> simp [hlt] <;> omega

private theorem r10_sumNat_beforeGt_eq_inv :
    ∀ (xs : List Nat), xs.Nodup → sumNat xs (fun v => r10_beforeGt xs v) = listInvCnt xs
  | [], _ => rfl
  | x :: rest, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [sumNat, listInvCnt]
    have hself : r10_beforeGt (x :: rest) x = 0 := by simp [r10_beforeGt]
    have hrest_eq :
        sumNat rest (fun v => r10_beforeGt (x :: rest) v) =
        sumNat rest (fun v => (if v < x then 1 else 0) + r10_beforeGt rest v) := by
      apply sumNat_congr
      intro v hv
      have hxv : x ≠ v := fun h => hnd.1 (h ▸ hv)
      simp [r10_beforeGt, hxv]
    have hcnt : sumNat rest (fun v => if v < x then 1 else 0) = rest.countP (fun v => decide (v < x)) := by
      rw [countP_eq_sumNat]
      apply sumNat_congr
      intro v _
      by_cases h : v < x <;> simp [h]
    rw [hself, hrest_eq, sumNat_add, hcnt, r10_sumNat_beforeGt_eq_inv rest hnd.2]
    omega

private theorem r10_nodup_westStep_append (stk rest : List Nat) (x : Nat) (stk_rem : List Nat)
    (hsplit : stk = (westStep stk x).1 ++ stk_rem)
    (hstk2 : (westStep stk x).2 = x :: stk_rem)
    (hnd : (stk ++ (x :: rest)).Nodup) :
    ((westStep stk x).1 ++ ((westStep stk x).2 ++ rest)).Nodup := by
  rw [hstk2]
  rw [hsplit, List.append_assoc] at hnd
  rw [List.nodup_append] at hnd ⊢
  rcases hnd with ⟨hpop_nd, hrem_x_nd, hdisj1⟩
  rw [List.nodup_append] at hrem_x_nd
  rcases hrem_x_nd with ⟨hrem_nd, hx_rest_nd, hdisj2⟩
  rw [List.nodup_cons] at hx_rest_nd
  refine ⟨hpop_nd, ?_, ?_⟩
  · simp only [List.cons_append, List.nodup_cons, List.mem_append, not_or]
    refine ⟨⟨fun hxm => hdisj2 x hxm x (by simp) rfl, hx_rest_nd.1⟩, ?_⟩
    exact List.nodup_append.mpr ⟨hrem_nd, hx_rest_nd.2, fun a ha b hb => hdisj2 a ha b (by simp [hb])⟩
  · intro a ha b hb
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hb
    rcases hb with rfl | hb_rem | hb_rest
    · exact hdisj1 a ha b (List.mem_append_right _ (by simp))
    · exact hdisj1 a ha b (List.mem_append_left _ hb_rem)
    · exact hdisj1 a ha b (List.mem_append_right _ (by simp [hb_rest]))

private theorem r10_mem_iff_countP_pos (xs : List Nat) (b : Nat) :
    b ∈ xs ↔ 1 ≤ xs.countP (fun z => decide (z = b)) := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.mem_cons, List.countP_cons]
    by_cases hxb : x = b
    · subst hxb
      simp only [decide_true, ↓reduceIte, true_or, true_iff]
      omega
    · have hbx : b ≠ x := Ne.symm hxb
      simp only [hxb, hbx, decide_false, Bool.false_eq_true, ↓reduceIte, false_or, Nat.add_zero]
      exact ih

private theorem r10_westSortAux_nodup :
    ∀ (xs stk : List Nat), stk.Pairwise (· ≤ ·) → (stk ++ xs).Nodup → (westSortAux xs stk).Nodup
  | [], _, _, hnd => by simpa [westSortAux] using hnd
  | x :: rest, stk, hstk, hnd => by
    rcases r10_westStep_spec stk x hstk with ⟨stk_rem, hsplit, hstk2, _, _, _, hstk2_pw⟩
    have hnd_all := r10_nodup_westStep_append stk rest x stk_rem hsplit hstk2 hnd
    rw [List.nodup_append] at hnd_all
    have ih := r10_westSortAux_nodup rest (westStep stk x).2 hstk2_pw hnd_all.2.1
    unfold westSortAux
    rw [List.nodup_append]
    refine ⟨hnd_all.1, ih, ?_⟩
    intro a ha b hb
    have hpos : 1 ≤ (westSortAux rest (westStep stk x).2).countP (fun z => decide (z = b)) :=
      (r10_mem_iff_countP_pos _ b).mp hb
    rw [r10_westSortAux_countP, ← List.countP_append] at hpos
    have hmem2 : b ∈ (westStep stk x).2 ++ rest := (r10_mem_iff_countP_pos _ b).mpr hpos
    exact hnd_all.2.2 a ha b hmem2

private theorem r10_beforeGt_pw_prefix_zero :
    ∀ (ps zs : List Nat) (v : Nat),
      ps.Pairwise (· ≤ ·) → v ∈ ps → r10_beforeGt (ps ++ zs) v = 0
  | [], _, _, _, hv => by simp at hv
  | p :: pr, zs, v, hpw, hv => by
    cases hpw with
    | cons hp hpr =>
      rcases List.mem_cons.mp hv with heq | hv_pr
      · subst heq; simp [r10_beforeGt]
      · have hpv : p ≤ v := hp v hv_pr
        have hng : ¬ (v < p) := by omega
        by_cases heq : p = v
        · simp [List.cons_append, r10_beforeGt, heq]
        · simp [List.cons_append, r10_beforeGt, heq, hng,
            r10_beforeGt_pw_prefix_zero pr zs v hpr hv_pr]

private theorem r10_beforeGt_zero_of_in_stk :
    ∀ (xs stk : List Nat) (v : Nat),
      stk.Pairwise (· ≤ ·) → (stk ++ xs).Nodup → v ∈ stk →
      r10_beforeGt (westSortAux xs stk) v = 0
  | [], stk, v, hstk, _, hv => by
    have h := r10_beforeGt_pw_prefix_zero stk [] v hstk hv
    simpa [westSortAux] using h
  | x :: rest, stk, v, hstk, hnd, hv => by
    rcases r10_westStep_spec stk x hstk with ⟨stk_rem, hsplit, hstk2, hpop_lt, hrem_ge, hpop_pw, hstk2_pw⟩
    have hnd_all := r10_nodup_westStep_append stk rest x stk_rem hsplit hstk2 hnd
    have hv_cases : v ∈ (westStep stk x).1 ∨ v ∈ stk_rem := by
      rw [hsplit] at hv
      exact List.mem_append.mp hv
    unfold westSortAux
    rcases hv_cases with hv_pop | hv_rem
    · exact r10_beforeGt_pw_prefix_zero (westStep stk x).1 _ v hpop_pw hv_pop
    · have hv_not_pop : v ∉ (westStep stk x).1 := by
        rw [List.nodup_append] at hnd_all
        intro hvp
        exact hnd_all.2.2 v hvp v (by rw [hstk2]; simp [hv_rem]) rfl
      have hxv : x ≤ v := hrem_ge v hv_rem
      have hpop_no_gt : ((westStep stk x).1).countP (fun z => decide (v < z)) = 0 :=
        r10_countP_zero_of_forall _ _ (fun z hz => decide_eq_false (by have := hpop_lt z hz; omega))
      rw [r10_beforeGt_append_not_mem _ _ v hv_not_pop, hpop_no_gt, Nat.zero_add]
      exact r10_beforeGt_zero_of_in_stk rest (westStep stk x).2 v hstk2_pw
        (List.nodup_append.mp hnd_all).2.1 (by rw [hstk2]; simp [hv_rem])

private theorem r10_beforeGt_westSortAux_inv :
    ∀ (xs stk : List Nat) (v : Nat),
      stk.Pairwise (· ≤ ·) → (stk ++ xs).Nodup → v ∈ xs →
      r10_beforeGt (westSortAux xs stk) v ≤ stk.countP (fun z => decide (v < z)) + r10_beforeGt xs v ∧
      ((1 ≤ stk.countP (fun z => decide (v < z)) ∨ 1 ≤ r10_beforeGt (westSortAux xs stk) v) →
        r10_beforeGt (westSortAux xs stk) v + 1 ≤ stk.countP (fun z => decide (v < z)) + r10_beforeGt xs v)
  | [], _, _, _, _, hv => by simp at hv
  | x :: rest, stk, v, hstk, hnd, hv => by
    rcases r10_westStep_spec stk x hstk with ⟨stk_rem, hsplit, hstk2, hpop_lt, _, _, hstk2_pw⟩
    have hnd_all := r10_nodup_westStep_append stk rest x stk_rem hsplit hstk2 hnd
    have hv_not_stk : v ∉ stk := by
      rw [List.nodup_append] at hnd
      exact fun hvs => hnd.2.2 v hvs v hv rfl
    have hv_not_pop : v ∉ (westStep stk x).1 := fun hvp =>
      hv_not_stk (by rw [hsplit]; exact List.mem_append_left _ hvp)
    rcases List.mem_cons.mp hv with heq_vx | hv_rest
    · subst heq_vx
      have hpop0 : ((westStep stk v).1).countP (fun z => decide (v < z)) = 0 :=
        r10_countP_zero_of_forall _ _ (fun z hz => decide_eq_false (by have := hpop_lt z hz; omega))
      have htail0 : r10_beforeGt (westSortAux rest (westStep stk v).2) v = 0 :=
        r10_beforeGt_zero_of_in_stk rest (westStep stk v).2 v hstk2_pw
          (List.nodup_append.mp hnd_all).2.1 (by rw [hstk2]; simp)
      unfold westSortAux
      rw [r10_beforeGt_append_not_mem _ _ v hv_not_pop, hpop0, htail0]
      simp only [r10_beforeGt, ↓reduceIte]
      exact ⟨by omega, fun h1 => by omega⟩
    · have hxv : x ≠ v := by
        rw [List.nodup_append] at hnd
        have hnd_xs := hnd.2.1
        rw [List.nodup_cons] at hnd_xs
        exact fun heq => hnd_xs.1 (heq ▸ hv_rest)
      have ih := r10_beforeGt_westSortAux_inv rest (westStep stk x).2 v hstk2_pw
        (List.nodup_append.mp hnd_all).2.1 hv_rest
      have hcnt_split :
          stk.countP (fun z => decide (v < z)) + (if v < x then 1 else 0) =
          ((westStep stk x).1).countP (fun z => decide (v < z)) +
          ((westStep stk x).2).countP (fun z => decide (v < z)) := by
        conv => lhs; rw [hsplit]
        rw [hstk2, List.countP_append, List.countP_cons]
        by_cases hlt : v < x <;> simp [hlt] <;> omega
      unfold westSortAux
      rw [r10_beforeGt_append_not_mem _ _ v hv_not_pop]
      simp only [r10_beforeGt, hxv, ↓reduceIte]
      by_cases hlt : v < x
      · have hstk2_ge1 : 1 ≤ ((westStep stk x).2).countP (fun z => decide (v < z)) := by
          rw [hstk2, List.countP_cons]
          simp [hlt]
        have ih2 := ih.2 (Or.inl hstk2_ge1)
        simp only [hlt, ↓reduceIte] at hcnt_split ⊢
        exact ⟨by omega, fun _ => by omega⟩
      · simp only [hlt, ↓reduceIte] at hcnt_split ⊢
        have hpop0 : ((westStep stk x).1).countP (fun z => decide (v < z)) = 0 :=
          r10_countP_zero_of_forall _ _ (fun z hz => decide_eq_false (by have := hpop_lt z hz; omega))
        refine ⟨by have := ih.1; omega, fun hdisj => ?_⟩
        have ih2 := ih.2 (by omega)
        omega

private theorem r10_westSortList_beforeGt_drop (xs : List Nat) (v : Nat) (hnd : xs.Nodup) (hv : v ∈ xs)
    (hpos : 1 ≤ r10_beforeGt (westSortList xs) v) :
    r10_beforeGt (westSortList xs) v + 1 ≤ r10_beforeGt xs v := by
  have h := (r10_beforeGt_westSortAux_inv xs [] v .nil (by simpa using hnd) hv).2 (Or.inr hpos)
  simpa [westSortList] using h

private def r10_mid31 : List Nat → Nat → Nat → Nat
  | [], _, _ => 0
  | b :: rest, a, v =>
    (if a < b ∧ v ∈ rest ∧ v < a then 1 else 0) + r10_mid31 rest a v

private def r10_end231 : List Nat → Nat → Nat
  | [], _ => 0
  | a :: rest, v => r10_mid31 rest a v + r10_end231 rest v

private theorem r10_mid31_not_mem (ys : List Nat) (a v : Nat) (hnot : v ∉ ys) :
    r10_mid31 ys a v = 0 := by
  induction ys with
  | nil => rfl
  | cons b yr ih =>
    have hnot_r : v ∉ yr := fun hm => hnot (by simp [hm])
    simp [r10_mid31, hnot_r, ih hnot_r]

private theorem r10_end231_not_mem (ys : List Nat) (v : Nat) (hnot : v ∉ ys) :
    r10_end231 ys v = 0 := by
  induction ys with
  | nil => rfl
  | cons a yr ih =>
    have hnot_r : v ∉ yr := fun hm => hnot (by simp [hm])
    simp [r10_end231, r10_mid31_not_mem yr a v hnot_r, ih hnot_r]

private theorem r10_sumNat_zero {α : Type} (ys : List α) :
    sumNat ys (fun _ => 0) = 0 := by
  induction ys with
  | nil => rfl
  | cons _ yr ih => simp [sumNat, ih]

private theorem r10_sumNat_mid31_eq_pairs31 :
    ∀ (ys : List Nat) (a : Nat), ys.Nodup → sumNat ys (fun v => r10_mid31 ys a v) = pairs31 ys a
  | [], _, _ => rfl
  | b :: yr, a, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [sumNat, pairs31]
    have hb0 : r10_mid31 (b :: yr) a b = 0 := by
      simp [r10_mid31, hnd.1, r10_mid31_not_mem yr a b hnd.1]
    have hyr_eq :
        sumNat yr (fun v => r10_mid31 (b :: yr) a v) =
        sumNat yr (fun v => (if a < b ∧ v < a then 1 else 0) + r10_mid31 yr a v) := by
      apply sumNat_congr
      intro v hv
      simp [r10_mid31, hv]
    have hcnt :
        sumNat yr (fun v => if a < b ∧ v < a then 1 else 0) =
        (if a < b then yr.countP (fun c => decide (c < a)) else 0) := by
      by_cases hab : a < b
      · simp only [hab, true_and, ↓reduceIte]
        rw [countP_eq_sumNat]
        apply sumNat_congr
        intro v _
        by_cases hva : v < a <;> simp [hva]
      · simp only [hab, false_and, ↓reduceIte]
        exact r10_sumNat_zero yr
    rw [hb0, hyr_eq, sumNat_add, hcnt, r10_sumNat_mid31_eq_pairs31 yr a hnd.2]
    omega

private theorem r10_sumNat_end231_eq_pat231 :
    ∀ (xs : List Nat), xs.Nodup → sumNat xs (fun v => r10_end231 xs v) = pat231List xs
  | [], _ => rfl
  | a :: rest, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [sumNat, pat231List]
    have ha0 : r10_end231 (a :: rest) a = 0 := by
      simp [r10_end231, r10_mid31_not_mem rest a a hnd.1, r10_end231_not_mem rest a hnd.1]
    have hrest_def :
        sumNat rest (fun v => r10_end231 (a :: rest) v) =
        sumNat rest (fun v => r10_mid31 rest a v + r10_end231 rest v) := rfl
    rw [ha0, Nat.zero_add, hrest_def, sumNat_add, r10_sumNat_mid31_eq_pairs31 rest a hnd.2,
        r10_sumNat_end231_eq_pat231 rest hnd.2]

private def r10_Avoids321List (xs : List Nat) : Prop :=
  ∀ a b c : Nat, [a, b, c].Sublist xs → ¬ (a > b ∧ b > c)

private theorem r10_beforeGt_le_mid31 :
    ∀ (ys : List Nat) (x v : Nat),
      (x :: ys).Nodup → v ∈ ys → v < x →
      (∀ b c : Nat, [b, c].Sublist ys → ¬ (x > b ∧ b > c)) →
      r10_beforeGt ys v ≤ r10_mid31 ys x v
  | [], _, _, _, hv, _, _ => by simp at hv
  | b :: yr, x, v, hnd, hv, hvx, hno => by
    have hnd_x := List.nodup_cons.mp hnd
    have hnd_b := List.nodup_cons.mp hnd_x.2
    have hxb : x ≠ b := fun h => hnd_x.1 (by simp [h])
    rcases List.mem_cons.mp hv with rfl | hvy
    · simp [r10_beforeGt]
    · have hbv : b ≠ v := fun h => hnd_b.1 (h ▸ hvy)
      have ih := r10_beforeGt_le_mid31 yr x v
        (List.nodup_cons.mpr ⟨fun hxm => hnd_x.1 (by simp [hxm]), hnd_b.2⟩) hvy hvx
        (fun b' c' hsub => hno b' c' (.cons b hsub))
      by_cases hvb : v < b
      · have hsub2 : [b, v].Sublist (b :: yr) :=
          .cons_cons b (List.singleton_sublist.mpr hvy)
        have hnot_bx : ¬ (b < x) := fun hbx => hno b v hsub2 ⟨hbx, hvb⟩
        have hxb_lt : x < b := by omega
        simp only [r10_beforeGt, hbv, hvb, ↓reduceIte, r10_mid31, hxb_lt, hvy, hvx, and_self]
        omega
      · simp only [r10_beforeGt, hbv, hvb, ↓reduceIte, r10_mid31]
        omega

private theorem r10_succ_choose2_eq (m : Nat) :
    (m + 1) * m = m * (m - 1) + 2 * m := by
  cases m with
  | zero => simp
  | succ k =>
    simp only [Nat.add_sub_cancel]
    calc (k + 1 + 1) * (k + 1)
        = (k + 1) * (k + 1) + 1 * (k + 1) := Nat.add_mul (k + 1) 1 (k + 1)
      _ = (k + 1) * k + (k + 1) * 1 + (k + 1) := by rw [Nat.mul_add (k + 1) k 1, Nat.one_mul]
      _ = (k + 1) * k + 2 * (k + 1) := by omega

private theorem r10_av321_choose2_le_end231 :
    ∀ (xs : List Nat) (v : Nat),
      xs.Nodup → r10_Avoids321List xs → v ∈ xs →
      r10_beforeGt xs v * (r10_beforeGt xs v - 1) ≤ 2 * r10_end231 xs v
  | [], _, _, _, hv => by simp at hv
  | x :: rest, v, hnd, h321, hv => by
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hv with rfl | hv_rest
    · simp [r10_beforeGt]
    · have hxv : x ≠ v := fun h => hnd.1 (h ▸ hv_rest)
      have h321_rest : r10_Avoids321List rest := fun a b c hsub => h321 a b c (.cons x hsub)
      have ih := r10_av321_choose2_le_end231 rest v hnd.2 h321_rest hv_rest
      by_cases hvx : v < x
      · have hmid := r10_beforeGt_le_mid31 rest x v
          (List.nodup_cons.mpr hnd) hv_rest hvx
          (fun b c hsub => h321 x b c (.cons_cons x hsub))
        have hbg : r10_beforeGt (x :: rest) v = r10_beforeGt rest v + 1 := by
          simp [r10_beforeGt, hxv, hvx, Nat.add_comm]
        rw [hbg, Nat.add_sub_cancel, r10_succ_choose2_eq, r10_end231]
        omega
      · have hbg : r10_beforeGt (x :: rest) v = r10_beforeGt rest v := by
          simp [r10_beforeGt, hxv, hvx]
        rw [hbg, r10_end231]
        omega

private theorem r10_six_mul_le_choose2 :
    ∀ (k m : Nat), 1 ≤ k → k + 2 ≤ m → 6 * k ≤ m * (m - 1) := by
  intro k m hk hkm
  have hk_base : 6 * k ≤ (k + 2) * (k + 1) := by
    clear hkm
    induction k with
    | zero => omega
    | succ t iht =>
      cases t with
      | zero => decide
      | succ t2 =>
        have hprev : 6 * (t2 + 1) ≤ (t2 + 3) * (t2 + 2) := iht (by omega)
        calc 6 * (t2 + 2) = 6 * (t2 + 1) + 6 := by omega
          _ ≤ (t2 + 3) * (t2 + 2) + 6 := by omega
          _ ≤ (t2 + 3) * (t2 + 2) + (2 * t2 + 6) := by omega
          _ = (t2 + 4) * (t2 + 3) := by
            calc (t2 + 3) * (t2 + 2) + (2 * t2 + 6)
                = (t2 + 3) * (t2 + 2) + (t2 + 3) + (t2 + 3) := by omega
              _ = (t2 + 3) * (t2 + 3) + 1 * (t2 + 3) := by rw [← Nat.mul_succ (t2 + 3) (t2 + 2), Nat.one_mul]
              _ = (t2 + 4) * (t2 + 3) := (Nat.add_mul (t2 + 3) 1 (t2 + 3)).symm
  have hmono : (k + 2) * (k + 1) ≤ m * (m - 1) := by
    have h1 : k + 2 ≤ m := hkm
    have h2 : k + 1 ≤ m - 1 := by omega
    exact Nat.mul_le_mul h1 h2
  exact Nat.le_trans hk_base hmono

private theorem r10_sublist_map_witness {α β : Type} (f : α → β) :
    ∀ {ys : List β} {L : List α}, ys.Sublist (L.map f) →
      ∃ xs : List α, xs.Sublist L ∧ xs.map f = ys
  | ys, [], h => by
    cases h
    exact ⟨[], .slnil, rfl⟩
  | ys, x :: xr, h => by
    simp only [List.map_cons] at h
    cases h with
    | cons _ h' =>
      rcases r10_sublist_map_witness f h' with ⟨xs, hsub, hmap⟩
      exact ⟨xs, .cons x hsub, hmap⟩
    | cons_cons _ h' =>
      rcases r10_sublist_map_witness f h' with ⟨xs, hsub, hmap⟩
      exact ⟨x :: xs, .cons_cons x hsub, by simp [hmap]⟩

private theorem r10_finRange_pairwise_lt (n : Nat) :
    (List.finRange n).Pairwise (fun i j : Fin n => i.val < j.val) := by
  have hval : ((List.finRange n).map Fin.val).Pairwise (· < ·) := by
    rw [finRange_map_val]
    exact List.pairwise_lt_range
  exact List.pairwise_map.mp hval

private theorem r10_perm_avoids321_list {n : Nat} (p : PermFin n) (h321 : p.Avoids321) :
    r10_Avoids321List p.toList := by
  intro a b c hsub
  rcases r10_sublist_map_witness (fun i : Fin n => (p.toFun i).val) hsub with ⟨xs, hxs_sub, hmap⟩
  cases xs with
  | nil => simp at hmap
  | cons i xr1 =>
    cases xr1 with
    | nil => simp at hmap
    | cons j xr2 =>
      cases xr2 with
      | nil => simp at hmap
      | cons k xr3 =>
        cases xr3 with
        | cons _ _ => simp at hmap
        | nil =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
          rcases hmap with ⟨ha, hb, hc⟩
          have hpw := (r10_finRange_pairwise_lt n).sublist hxs_sub
          have hij : i.val < j.val := (List.pairwise_cons.mp hpw).1 j (by simp)
          have hjk : j.val < k.val := (List.pairwise_cons.mp (List.pairwise_cons.mp hpw).2).1 k (by simp)
          rw [← ha, ← hb, ← hc]
          exact h321 i j k hij hjk

private theorem r10_nodup_map_inj {α β : Type} (f : α → β) (xs : List α) (hnd : xs.Nodup)
    (hinj : ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xr ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih hnd.2 (fun a ha b hb => hinj a (by simp [ha]) b (by simp [hb]))⟩
    rintro ⟨y, hy, hfy⟩
    have hyx := hinj y (by simp [hy]) x (by simp) hfy
    exact hnd.1 (hyx ▸ hy)

private theorem r10_perm_toList_nodup {n : Nat} (p : PermFin n) : p.toList.Nodup := by
  unfold PermFin.toList
  apply r10_nodup_map_inj _ (List.finRange n) (List.nodup_finRange n)
  intro a _ b _ hval
  exact p.toFun_inj (Fin.ext hval)

private theorem r10_sumNat_eq_of_nodup_subset {ys zs : List Nat} (g : Nat → Nat)
    (hy : ys.Nodup) (hz : zs.Nodup) (hyz : ∀ x, x ∈ ys ↔ x ∈ zs) :
    sumNat ys g = sumNat zs g := by
  have h1 : sumNat ys g = sumNat ys (fun x => sumNat zs (fun y => if y = x then g x else 0)) := by
    apply sumNat_congr
    intro x hx
    have hxz : x ∈ zs := (hyz x).mp hx
    have hm := sumNat_const_mul (g x) zs (fun y => if y = x then 1 else 0)
    rw [sumNat_eq_indicator_one zs hz x hxz, Nat.mul_one] at hm
    refine hm.trans (sumNat_congr zs _ _ fun y _ => ?_)
    by_cases h : y = x <;> simp [h]
  have h2 : sumNat zs g = sumNat zs (fun y => sumNat ys (fun x => if y = x then g x else 0)) := by
    apply sumNat_congr
    intro y hy_mem
    have hy_in : y ∈ ys := (hyz y).mpr hy_mem
    have hm := sumNat_const_mul (g y) ys (fun x => if x = y then 1 else 0)
    rw [sumNat_eq_indicator_one ys hy y hy_in, Nat.mul_one] at hm
    refine hm.trans (sumNat_congr ys _ _ fun x _ => ?_)
    by_cases h : x = y
    · subst h; simp
    · have hne : y ≠ x := fun h' => h h'.symm
      simp [h, hne]
  rw [h1, h2, sumNat_swap]

private theorem r10_westSortList_mem_iff (xs : List Nat) (v : Nat) :
    v ∈ westSortList xs ↔ v ∈ xs := by
  rw [r10_mem_iff_countP_pos, r10_mem_iff_countP_pos]
  unfold westSortList
  rw [r10_westSortAux_countP]
  simp

/-- **Round-10 Theorem 20 (Solution to `Conj_Av321_TwoStackInv_Pat231`):**
    Every `321`-avoiding permutation `p : PermFin n` satisfies `3 * p.stack2Inv ≤ p.pat231`,
    proved universally over all `n : Nat`. -/
theorem PermFin.avoids321_three_stack2Inv_le_pat231 {n : Nat} (p : PermFin n)
    (h321 : p.Avoids321) :
    3 * p.stack2Inv ≤ p.pat231 := by
  let L0 := p.toList
  let L1 := westSortList L0
  let L2 := westSortList L1
  have hnd0 : L0.Nodup := r10_perm_toList_nodup p
  have hnd1 : L1.Nodup := r10_westSortAux_nodup L0 [] .nil (by simpa using hnd0)
  have hnd2 : L2.Nodup := r10_westSortAux_nodup L1 [] .nil (by simpa using hnd1)
  have hmem01 : ∀ v, v ∈ L1 ↔ v ∈ L0 := r10_westSortList_mem_iff L0
  have hmem12 : ∀ v, v ∈ L2 ↔ v ∈ L1 := r10_westSortList_mem_iff L1
  have hmem02 : ∀ v, v ∈ L2 ↔ v ∈ L0 := fun v => (hmem12 v).trans (hmem01 v)
  have hinv2 : p.stack2Inv = sumNat L0 (fun v => r10_beforeGt L2 v) := by
    unfold PermFin.stack2Inv
    change listInvCnt L2 = _
    rw [← r10_sumNat_beforeGt_eq_inv L2 hnd2]
    exact r10_sumNat_eq_of_nodup_subset _ hnd2 hnd0 hmem02
  have hpat : p.pat231 = sumNat L0 (fun v => r10_end231 L0 v) := by
    unfold PermFin.pat231
    exact (r10_sumNat_end231_eq_pat231 L0 hnd0).symm
  have h321_L0 : r10_Avoids321List L0 := r10_perm_avoids321_list p h321
  rw [hinv2, sumNat_const_mul, hpat]
  apply sumNat_mono
  intro v hv0
  by_cases hk : r10_beforeGt L2 v = 0
  · rw [hk]
    exact Nat.zero_le _
  · have hk1 : 1 ≤ r10_beforeGt L2 v := by omega
    have hv1 : v ∈ L1 := (hmem01 v).mpr hv0
    have hdrop2 : r10_beforeGt L2 v + 1 ≤ r10_beforeGt L1 v :=
      r10_westSortList_beforeGt_drop L1 v hnd1 hv1 hk1
    have h1_pos : 1 ≤ r10_beforeGt L1 v := by omega
    have hdrop1 : r10_beforeGt L1 v + 1 ≤ r10_beforeGt L0 v :=
      r10_westSortList_beforeGt_drop L0 v hnd0 hv0 h1_pos
    have h6k : 6 * r10_beforeGt L2 v ≤ r10_beforeGt L0 v * (r10_beforeGt L0 v - 1) :=
      r10_six_mul_le_choose2 (r10_beforeGt L2 v) (r10_beforeGt L0 v) hk1 (by omega)
    have hch2 := r10_av321_choose2_le_end231 L0 v hnd0 h321_L0 hv0
    omega

-- ============================================================================
-- 21. Graph Independence + Domination, Ore's 2*gamma <= n, Geodesic & Clique Bounds
-- ============================================================================

private theorem r10p2_length_filter_eq_countP {α : Type} (p : α → Bool) (xs : List α) :
    (xs.filter p).length = xs.countP p := by
  induction xs with
  | nil => rfl
  | cons x xr ih =>
    simp only [List.filter_cons, List.countP_cons]
    cases p x <;> simp [ih] <;> omega

private theorem r10p2_nodup_singleton {α : Type} (x : α) : ([x] : List α).Nodup := by
  simp

private theorem r10p2_nodup_map_inj {α β : Type} (f : α → β) (xs : List α) (hnd : xs.Nodup)
    (hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a ar ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih hnd.2 (fun x hx y hy hxy => hinj x (by simp [hx]) y (by simp [hy]) hxy)⟩
    rintro ⟨b, hb, hfb⟩
    have hab := hinj b (by simp [hb]) a (by simp) hfb
    exact hnd.1 (hab ▸ hb)

private theorem r10p2_getLast?_append_of_ne_nil {α : Type} (A B : List α) (hB : B ≠ []) :
    (A ++ B).getLast? = B.getLast? := by
  induction A with
  | nil => rfl
  | cons a ar ih =>
    have hne : ar ++ B ≠ [] := fun h => hB (List.append_eq_nil_iff.mp h).2
    cases hAB : ar ++ B with
    | nil => exact absurd hAB hne
    | cons c cr =>
      have h1 : (a :: (c :: cr)).getLast? = (c :: cr).getLast? := rfl
      rw [List.cons_append, hAB, h1, ← hAB, ih]

private theorem r10p2_sublist_map_witness {α β : Type} (f : α → β) :
    ∀ {ys : List β} {B : List α}, ys.Sublist (B.map f) →
      ∃ xs : List α, xs.Sublist B ∧ xs.map f = ys
  | _, [], h => by cases h; exact ⟨[], .slnil, rfl⟩
  | _, b :: br, h => by
    simp only [List.map_cons] at h
    cases h with
    | cons _ h' =>
      rcases r10p2_sublist_map_witness f h' with ⟨xs, hs', hm'⟩
      exact ⟨xs, .cons b hs', hm'⟩
    | cons_cons _ h' =>
      rcases r10p2_sublist_map_witness f h' with ⟨xs, hs', hm'⟩
      exact ⟨b :: xs, .cons_cons b hs', by simp [hm']⟩

private theorem r10p2_mem_sumNat_pos {α : Type} (p : α → Bool) (xs : List α) (u : α)
    (hu : u ∈ xs) (hp : p u = true) :
    1 ≤ sumNat xs (fun x => if p x then 1 else 0) := by
  induction xs with
  | nil => simp at hu
  | cons z zr ih =>
    simp only [sumNat]
    rcases List.mem_cons.mp hu with rfl | hzr
    · simp [hp]
    · have := ih hzr; omega

private theorem r10p2_foldl_max_ge {α : Type} (f : α → Nat) (xs : List α) (init : Nat) :
    init ≤ xs.foldl (fun acc w => max acc (f w)) init ∧
    ∀ x ∈ xs, f x ≤ xs.foldl (fun acc w => max acc (f w)) init := by
  induction xs generalizing init with
  | nil => exact ⟨Nat.le_refl _, fun _ h => by simp at h⟩
  | cons y rest ih =>
    rcases ih (max init (f y)) with ⟨h1, h2⟩
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hr
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 x hr

theorem SimpleGraphFin.deg_le_maxDeg {n : Nat} (G : SimpleGraphFin n) (v : Fin n) :
    G.deg v ≤ G.maxDeg :=
  (r10p2_foldl_max_ge G.deg (List.finRange n) 0).2 v (List.mem_finRange v)

private theorem r10p2_nodup_length_eq_countP_finRange {n : Nat} (S : List (Fin n)) (hnd : S.Nodup) :
    S.length = (List.finRange n).countP (fun v => decide (v ∈ S)) := by
  have h1 : S.length = sumNat S (fun x => sumNat (List.finRange n) (fun v => if v = x then 1 else 0)) := by
    induction S with
    | nil => rfl
    | cons x sr ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.length_cons, sumNat]
      rw [sumNat_eq_indicator_one (List.finRange n) (List.nodup_finRange n) x (List.mem_finRange x),
          ih hnd.2]
      omega
  rw [h1, sumNat_swap, countP_eq_sumNat]
  apply sumNat_congr
  intro v _
  by_cases hv : v ∈ S
  · have hm := sumNat_eq_indicator_one S hnd v hv
    have hc : sumNat S (fun x => if v = x then 1 else 0) = sumNat S (fun x => if x = v then 1 else 0) := by
      apply sumNat_congr; intro x _; by_cases h : v = x
      · subst h; simp
      · have h' : x ≠ v := Ne.symm h; simp [h, h']
    rw [hc, hm]
    simp [hv]
  · have hz : sumNat S (fun x => if v = x then 1 else 0) = 0 := by
      clear h1 hnd
      induction S with
      | nil => rfl
      | cons x sr ih =>
        have hvx : v ≠ x := fun h => hv (by simp [h])
        have hvsr : v ∉ sr := fun hm => hv (by simp [hm])
        simp [sumNat, hvx, ih hvsr]
    rw [hz]
    simp [hv]

private theorem r10p2_compl_length_add {n : Nat} (S : List (Fin n)) (hnd : S.Nodup) :
    S.length + ((List.finRange n).filter (fun v => decide (v ∉ S))).length = n := by
  rw [r10p2_nodup_length_eq_countP_finRange S hnd, r10p2_length_filter_eq_countP]
  rw [countP_eq_sumNat, countP_eq_sumNat, ← sumNat_add]
  have h1 : sumNat (List.finRange n)
      (fun x => (if decide (x ∈ S) = true then 1 else 0) + (if decide (x ∉ S) = true then 1 else 0)) =
      sumNat (List.finRange n) (fun _ => 1) := by
    apply sumNat_congr
    intro x _
    by_cases hx : x ∈ S <;> simp [hx]
  rw [h1]
  have hlen : ∀ L : List (Fin n), sumNat L (fun _ => 1) = L.length := by
    intro L; induction L with | nil => rfl | cons _ lr ih => simp [sumNat, ih]; omega
  rw [hlen, List.length_finRange]

private theorem r10p2_exists_adj_of_deg_pos {n : Nat} (G : SimpleGraphFin n) (v : Fin n)
    (hd : 1 ≤ G.deg v) : ∃ u : Fin n, G.adj v u = true := by
  unfold SimpleGraphFin.deg at hd
  have hne : (List.finRange n).filter (G.adj v) ≠ [] := by
    intro hnil
    rw [← r10p2_length_filter_eq_countP, hnil] at hd
    simp at hd
  cases hf : (List.finRange n).filter (G.adj v) with
  | nil => exact absurd hf hne
  | cons u _ =>
    have hm : u ∈ (List.finRange n).filter (G.adj v) := by rw [hf]; simp
    exact ⟨u, (List.mem_filter.mp hm).2⟩

theorem SimpleGraphFin.noIsolates_of_connected {n : Nat} (G : SimpleGraphFin n)
    (hn : 2 ≤ n) (hConn : G.Connected) : ∀ v : Fin n, 1 ≤ G.deg v := by
  intro v
  let w : Fin n := if v.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hvw : v ≠ w := by
    dsimp [w]
    by_cases hv0 : v.val = 0
    · simp only [hv0, ↓reduceIte]; intro h; have := congrArg Fin.val h; simp [hv0] at this
    · simp only [hv0, ↓reduceIte]; intro h; exact hv0 (congrArg Fin.val h)
  rcases hConn v w with ⟨walk, hne, hhead, hlast, hwalk⟩
  cases walk with
  | nil => exact absurd rfl hne
  | cons a wr =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases wr with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      exact absurd hlast hvw
    | cons u _ =>
      unfold SimpleGraphFin.deg
      rw [countP_eq_sumNat]
      exact r10p2_mem_sumNat_pos (G.adj a) (List.finRange n) u (List.mem_finRange u) hwalk.1

/-- **Round-10 Theorem 21a (Gallai-Ore Independence + Domination Bound):**
    In every finite graph without isolated vertices, `α(G) + γ(G) ≤ n`. -/
theorem SimpleGraphFin.indep_add_dom_le_of_noIsolates {n a g : Nat} (G : SimpleGraphFin n)
    (hIso : ∀ v : Fin n, 1 ≤ G.deg v) (ha : G.IndependenceNum a) (hg : G.DominationNum g) :
    a + g ≤ n := by
  rcases ha.1 with ⟨S, hS, hSlen⟩
  let C := (List.finRange n).filter (fun v => decide (v ∉ S))
  have hsum := r10p2_compl_length_add S hS.1
  have hC_dom : G.IsDominatingSet C := by
    refine ⟨(List.nodup_finRange n).filter _, fun v => ?_⟩
    by_cases hv : v ∈ S
    · right
      rcases r10p2_exists_adj_of_deg_pos G v (hIso v) with ⟨u, huv⟩
      have hu_notin : u ∉ S := fun huS => by
        have hf := hS.2 v hv u huS
        rw [huv] at hf; cases hf
      refine ⟨u, List.mem_filter.mpr ⟨List.mem_finRange u, decide_eq_true hu_notin⟩, ?_⟩
      rw [G.symm]; exact huv
    · left
      exact List.mem_filter.mpr ⟨List.mem_finRange v, decide_eq_true hv⟩
  have hg_le := hg.2 C hC_dom
  dsimp only [C] at hg_le
  omega

theorem SimpleGraphFin.connected_alpha_add_dom_le {n a g : Nat} (G : SimpleGraphFin n)
    (hn : 2 ≤ n) (hConn : G.Connected) (ha : G.IndependenceNum a) (hg : G.DominationNum g) :
    a + g ≤ n :=
  G.indep_add_dom_le_of_noIsolates (G.noIsolates_of_connected hn hConn) ha hg

/-- **Round-10 Theorem 21b (Ore's Domination Theorem, 1962):**
    In every finite graph without isolated vertices, `2 * γ(G) ≤ n`. -/
theorem SimpleGraphFin.two_mul_dom_le_of_noIsolates {n g : Nat} (G : SimpleGraphFin n)
    (hIso : ∀ v : Fin n, 1 ≤ G.deg v) (hg : G.DominationNum g) :
    2 * g ≤ n := by
  rcases hg.1 with ⟨D, hD, hDlen⟩
  let C := (List.finRange n).filter (fun v => decide (v ∉ D))
  have hsum := r10p2_compl_length_add D hD.1
  have hC_dom : G.IsDominatingSet C := by
    refine ⟨(List.nodup_finRange n).filter _, fun v => ?_⟩
    by_cases hv : v ∈ D
    · right
      apply Classical.byContradiction
      intro hnoC
      rcases r10p2_exists_adj_of_deg_pos G v (hIso v) with ⟨z, hvz⟩
      have hzv_ne : z ≠ v := fun heq => by subst heq; rw [G.loopless] at hvz; cases hvz
      have hzD : z ∈ D := by
        apply Classical.byContradiction
        intro hz_not
        exact hnoC ⟨z, List.mem_filter.mpr ⟨List.mem_finRange z, decide_eq_true hz_not⟩, by rw [G.symm]; exact hvz⟩
      have hDer_dom : G.IsDominatingSet (D.erase v) := by
        refine ⟨hD.1.erase v, fun y => ?_⟩
        by_cases hyv : y = v
        · subst hyv
          exact Or.inr ⟨z, (List.mem_erase_of_ne hzv_ne).mpr hzD, by rw [G.symm]; exact hvz⟩
        · by_cases hyD : y ∈ D
          · exact Or.inl ((List.mem_erase_of_ne hyv).mpr hyD)
          · rcases hD.2 y with hy_in | ⟨u, huD, huy⟩
            · exact absurd hy_in hyD
            · have huv_ne : u ≠ v := fun heq => by
                subst heq
                exact hnoC ⟨y, List.mem_filter.mpr ⟨List.mem_finRange y, decide_eq_true hyD⟩, by rw [G.symm]; exact huy⟩
              exact Or.inr ⟨u, (List.mem_erase_of_ne huv_ne).mpr huD, huy⟩
      have hmin := hg.2 (D.erase v) hDer_dom
      have hlen_er := List.length_erase_of_mem hv
      have hposD : 1 ≤ D.length := by
        cases D with | nil => simp at hv | cons _ _ => simp
      omega
    · left
      exact List.mem_filter.mpr ⟨List.mem_finRange v, decide_eq_true hv⟩
  have hg_le := hg.2 C hC_dom
  dsimp only [C] at hg_le
  omega

theorem SimpleGraphFin.connected_two_mul_dom_le {n g : Nat} (G : SimpleGraphFin n)
    (hn : 2 ≤ n) (hConn : G.Connected) (hg : G.DominationNum g) :
    2 * g ≤ n :=
  G.two_mul_dom_le_of_noIsolates (G.noIsolates_of_connected hn hConn) hg

private theorem r10p2_walk_leaves_set {n : Nat} (G : SimpleGraphFin n) (S : List (Fin n))
    (walk : List (Fin n)) (hs : ∀ s, walk.head? = some s → s ∈ S)
    (ht : ∀ t, walk.getLast? = some t → t ∉ S) (hw : G.IsWalk walk) (hne : walk ≠ []) :
    ∃ a ∈ S, ∃ b : Fin n, b ∉ S ∧ G.adj a b = true := by
  induction walk with
  | nil => exact False.elim (hne rfl)
  | cons x rest ih =>
    cases rest with
    | nil => exact False.elim (ht x rfl (hs x rfl))
    | cons y ys =>
      by_cases hy : y ∈ S
      · exact ih (fun s h => by simp at h; subst h; exact hy)
          (fun t h => ht t (by simpa using h)) hw.2 (by simp)
      · exact ⟨x, hs x rfl, y, hy, hw.1⟩

/-- **Round-10 Theorem 21c (Connected Non-Complete Clique vs. Max Degree):**
    In every connected non-complete graph `G`, `ω(G) ≤ Δ(G)`. -/
theorem SimpleGraphFin.clique_le_maxDeg_of_connected_notComplete {n w : Nat}
    (G : SimpleGraphFin n) (hConn : G.Connected)
    (hNotCmp : ∃ x y : Fin n, x ≠ y ∧ G.adj x y = false) (hw : G.CliqueNum w) :
    w ≤ G.maxDeg := by
  rcases hw.1 with ⟨K, hK, hKlen⟩
  cases hKeq : K with
  | nil => rw [← hKlen, hKeq]; simp
  | cons k0 kr =>
    rcases hNotCmp with ⟨x, y, hxy, hnadj⟩
    have hex_out : ∃ z : Fin n, z ∉ K := by
      by_cases hx : x ∈ K
      · by_cases hy : y ∈ K
        · have hadj := hK.2 x hx y hy hxy
          rw [hadj] at hnadj; cases hnadj
        · exact ⟨y, hy⟩
      · exact ⟨x, hx⟩
    rcases hex_out with ⟨z, hz⟩
    have hk0_in : k0 ∈ K := by rw [hKeq]; simp
    rcases hConn k0 z with ⟨walk, hne, hhead, hlast, hwalk⟩
    rcases r10p2_walk_leaves_set G K walk
      (fun s hs => by rw [hs] at hhead; injection hhead with h; subst h; exact hk0_in)
      (fun t ht => by rw [ht] at hlast; injection hlast with h; subst h; exact hz)
      hwalk hne with ⟨u, huK, v, hvK, huv⟩
    let Nlist := (K.erase u) ++ [v]
    have hN_nd : Nlist.Nodup := by
      rw [List.nodup_append]
      refine ⟨hK.1.erase u, r10p2_nodup_singleton v, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      intro heq; subst heq
      exact hvK (List.mem_of_mem_erase ha)
    have hN_len : Nlist.length = w := by
      dsimp [Nlist]
      rw [List.length_append, List.length_singleton, List.length_erase_of_mem huK]
      have hpos : 1 ≤ K.length := by rw [hKeq]; simp
      omega
    have hle_deg : Nlist.length ≤ G.deg u := by
      unfold SimpleGraphFin.deg
      have hN_cnt : Nlist.countP (fun _ => true) = Nlist.length := by simp
      rw [← hN_cnt]
      exact countP_map_le id (fun _ _ h => h) Nlist (List.finRange n) hN_nd (List.nodup_finRange n)
        (fun _ => true) (G.adj u) (fun a ha _ => by
          refine ⟨List.mem_finRange a, ?_⟩
          rcases List.mem_append.mp ha with ha_er | ha_v
          · have ha_ne : a ≠ u := fun heq => by
              subst heq
              exact (List.Nodup.not_mem_erase hK.1) ha_er
            exact hK.2 u huK a (List.mem_of_mem_erase ha_er) ha_ne.symm
          · simp only [List.mem_singleton] at ha_v
            subst ha_v; exact huv)
    exact Nat.le_trans (hN_len ▸ hle_deg) (G.deg_le_maxDeg u)

private def r10p2_nthOr {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | x :: _, 0, _ => x
  | _ :: xs, k + 1, d => r10p2_nthOr xs k d

private theorem r10p2_take_drop_geodesic {n : Nat} (G : SimpleGraphFin n) (W : List (Fin n)) (u0 v0 : Fin n)
    (hne : W ≠ []) (hhead : W.head? = some u0) (hlast : W.getLast? = some v0)
    (hw : G.IsWalk W) :
    (∀ i j : Nat, i < j → j < W.length → r10p2_nthOr W i u0 = r10p2_nthOr W j u0 →
      ∃ W' : List (Fin n), W' ≠ [] ∧ W'.head? = some u0 ∧ W'.getLast? = some v0 ∧ G.IsWalk W' ∧ W'.length < W.length) ∧
    (∀ i j : Nat, i + 2 ≤ j → j < W.length → G.adj (r10p2_nthOr W i u0) (r10p2_nthOr W j u0) = true →
      ∃ W' : List (Fin n), W' ≠ [] ∧ W'.head? = some u0 ∧ W'.getLast? = some v0 ∧ G.IsWalk W' ∧ W'.length < W.length) := by
  have hwalk_drop : ∀ (L : List (Fin n)) (k : Nat), G.IsWalk L → G.IsWalk (L.drop k) := by
    intro L k hL
    induction k generalizing L with
    | zero => simpa using hL
    | succ k ih =>
      cases L with
      | nil => simp [SimpleGraphFin.IsWalk]
      | cons a lr =>
        cases lr with
        | nil => simp [SimpleGraphFin.IsWalk]
        | cons b lr2 => exact ih (b :: lr2) hL.2
  have hdrop_cons : ∀ (L : List (Fin n)) (k : Nat), k < L.length →
      L.drop k = r10p2_nthOr L k u0 :: L.drop (k + 1) := by
    intro L k hk
    induction L generalizing k with
    | nil => simp at hk
    | cons a lr ih =>
      cases k with
      | zero => simp [r10p2_nthOr]
      | succ k' => simp [r10p2_nthOr, ih k' (by simp at hk; omega)]
  have hlast_drop : ∀ (L : List (Fin n)) (k : Nat), k < L.length → L.getLast? = some v0 →
      (L.drop k).getLast? = some v0 := by
    intro L k hk hl
    induction k generalizing L with
    | zero => simpa using hl
    | succ k' ih =>
      cases L with
      | nil => simp at hk
      | cons a lr =>
        cases lr with
        | nil => simp at hk
        | cons b lr2 => exact ih (b :: lr2) (by simp at hk; omega) (by simpa using hl)
  have hwalk_glue : ∀ (A B : List (Fin n)) (x y : Fin n),
      G.IsWalk (A ++ [x]) → G.IsWalk (y :: B) → G.adj x y = true →
      G.IsWalk ((A ++ [x]) ++ (y :: B)) := by
    intro A B x y hA hB hxy
    induction A with
    | nil => exact ⟨hxy, hB⟩
    | cons a ar ih =>
      cases ar with
      | nil => exact ⟨hA.1, hxy, hB⟩
      | cons a2 ar2 => exact ⟨hA.1, ih hA.2⟩
  have htake_succ : ∀ (L : List (Fin n)) (k : Nat), k < L.length →
      L.take (k + 1) = L.take k ++ [r10p2_nthOr L k u0] := by
    intro L k hk
    induction L generalizing k with
    | nil => simp at hk
    | cons a lr ih =>
      cases k with
      | zero => simp [r10p2_nthOr]
      | succ k' => simp [r10p2_nthOr, ih k' (by simp at hk; omega)]
  have hwalk_prefix : ∀ (A B : List (Fin n)), G.IsWalk (A ++ B) → G.IsWalk A := by
    intro A B hAB
    induction A with
    | nil => trivial
    | cons a ar ih =>
      cases ar with
      | nil => trivial
      | cons a2 ar2 => exact ⟨hAB.1, ih hAB.2⟩
  have hwalk_take : ∀ (k : Nat), G.IsWalk (W.take k) := by
    intro k
    have hw' : G.IsWalk (W.take k ++ W.drop k) := by rw [List.take_append_drop]; exact hw
    exact hwalk_prefix (W.take k) (W.drop k) hw'
  constructor
  · intro i j hij hj heq
    let W' := W.take i ++ W.drop j
    have hd_j := hdrop_cons W j hj
    refine ⟨W', ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [W']; rw [hd_j]; intro h; cases i <;> simp at h
    · cases i with
      | zero =>
        simp only [W', List.take_zero, List.nil_append, hd_j, List.head?_cons, ← heq]
        cases W with | nil => exact absurd rfl hne | cons a _ => simpa [r10p2_nthOr] using hhead
      | succ i' =>
        cases W with
        | nil => exact absurd rfl hne
        | cons a wr => simpa [W'] using hhead
    · have hl_j := hlast_drop W j hj hlast
      have hne_dj : W.drop j ≠ [] := by rw [hd_j]; simp
      dsimp [W']
      rw [r10p2_getLast?_append_of_ne_nil _ _ hne_dj]
      exact hl_j
    · cases i with
      | zero => simpa [W'] using hwalk_drop W j hw
      | succ i' =>
        have hti := htake_succ W i' (by omega)
        have hd1 := hdrop_cons W i' (by omega)
        have hd2 := hdrop_cons W (i' + 1) (by omega)
        have hwd := hwalk_drop W i' hw
        rw [hd1, hd2] at hwd
        have hadj_i : G.adj (r10p2_nthOr W i' u0) (r10p2_nthOr W (i' + 1) u0) = true := hwd.1
        have hadj_ij : G.adj (r10p2_nthOr W i' u0) (r10p2_nthOr W j u0) = true := heq ▸ hadj_i
        have hwi_only : G.IsWalk (W.take i' ++ [r10p2_nthOr W i' u0]) :=
          hti ▸ hwalk_take (i' + 1)
        have hw_dj : G.IsWalk (r10p2_nthOr W j u0 :: W.drop (j + 1)) := hd_j ▸ hwalk_drop W j hw
        dsimp [W']
        rw [hti, hd_j]
        exact hwalk_glue (W.take i') (W.drop (j + 1)) _ _ hwi_only hw_dj hadj_ij
    · dsimp [W']
      rw [List.length_append, List.length_take_of_le (by omega), List.length_drop]
      omega
  · intro i j hij hj hadj
    let W' := W.take (i + 1) ++ W.drop j
    have hd_j := hdrop_cons W j hj
    have hti := htake_succ W i (by omega)
    refine ⟨W', ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [W']; rw [hti]; simp
    · cases W with
      | nil => exact absurd rfl hne
      | cons a wr => simpa [W'] using hhead
    · have hl_j := hlast_drop W j hj hlast
      have hne_dj : W.drop j ≠ [] := by rw [hd_j]; simp
      dsimp [W']
      rw [r10p2_getLast?_append_of_ne_nil _ _ hne_dj]
      exact hl_j
    · have hwi : G.IsWalk (W.take i ++ [r10p2_nthOr W i u0]) := hti ▸ hwalk_take (i + 1)
      have hw_dj : G.IsWalk (r10p2_nthOr W j u0 :: W.drop (j + 1)) := hd_j ▸ hwalk_drop W j hw
      dsimp [W']
      rw [hti, hd_j]
      exact hwalk_glue (W.take i) (W.drop (j + 1)) _ _ hwi hw_dj hadj
    · dsimp [W']
      rw [List.length_append, List.length_take_of_le (by omega), List.length_drop]
      omega

private theorem r10p2_geodesic_exists {n d : Nat} (G : SimpleGraphFin n)
    (hd : G.DiameterNum d) (hdpos : 1 ≤ d) :
    ∃ (u0 : Fin n) (W : List (Fin n)),
      W.length = d + 1 ∧
      (∀ i j : Nat, i < j → j < d + 1 → r10p2_nthOr W i u0 ≠ r10p2_nthOr W j u0) ∧
      (∀ i j : Nat, i + 2 ≤ j → j < d + 1 → G.adj (r10p2_nthOr W i u0) (r10p2_nthOr W j u0) = false) := by
  have hnot_all : ¬ ∀ s t : Fin n, G.WithinDist s t (d - 1) := fun hall => by
    have := hd.2 (d - 1) hall; omega
  have ⟨u0, hu⟩ := Classical.not_forall.mp hnot_all
  have ⟨v0, hno⟩ := Classical.not_forall.mp hu
  rcases hd.1 u0 v0 with ⟨W, hne, hhead, hlast, hw, hlen_le⟩
  have hlen_ge : d + 1 ≤ W.length :=
    Classical.byContradiction fun hlt => hno ⟨W, hne, hhead, hlast, hw, by omega⟩
  have hlen : W.length = d + 1 := by omega
  have ⟨hrep, hshort⟩ := r10p2_take_drop_geodesic G W u0 v0 hne hhead hlast hw
  refine ⟨u0, W, hlen, ?_, ?_⟩
  · intro i j hij hj heq
    rcases hrep i j hij (by omega) heq with ⟨W', h1, h2, h3, h4, h5⟩
    exact hno ⟨W', h1, h2, h3, h4, by omega⟩
  · intro i j hij hj
    cases hadj : G.adj (r10p2_nthOr W i u0) (r10p2_nthOr W j u0)
    · rfl
    · exfalso
      rcases hshort i j hij (by omega) hadj with ⟨W', h1, h2, h3, h4, h5⟩
      exact hno ⟨W', h1, h2, h3, h4, by omega⟩

/-- **Round-10 Theorem 21d (`diam + 1 ≤ 2 * alpha`):**
    In every nonempty connected graph `G`, alternating vertices along a diametral path form
    an independent set of size `⌊d/2⌋ + 1`, giving `d + 1 ≤ 2 * α(G)`. -/
theorem SimpleGraphFin.connected_diam_add_one_le_two_mul_alpha {n d a : Nat}
    (G : SimpleGraphFin n) (hn : 1 ≤ n) (hd : G.DiameterNum d) (ha : G.IndependenceNum a) :
    d + 1 ≤ 2 * a := by
  by_cases hd0 : d = 0
  · subst hd0
    let v0 : Fin n := ⟨0, hn⟩
    have hS : G.IsIndepSet [v0] := ⟨r10p2_nodup_singleton v0, fun u hu v hv => by
      simp at hu hv; subst hu; subst hv; exact G.loopless v0⟩
    have hle := ha.2 [v0] hS
    simp at hle; omega
  · rcases r10p2_geodesic_exists G hd (by omega) with ⟨u0, W, _, hno_rep, hno_short⟩
    let m := d / 2 + 1
    let S := (List.range m).map (fun k => r10p2_nthOr W (2 * k) u0)
    have hS_nd : S.Nodup := by
      apply r10p2_nodup_map_inj _ (List.range m) List.nodup_range
      intro i hi j hj heq
      have him : i < m := List.mem_range.mp hi
      have hjm : j < m := List.mem_range.mp hj
      by_cases hij : i < j
      · exact False.elim (hno_rep (2 * i) (2 * j) (by omega) (by omega) heq)
      · by_cases hji : j < i
        · exact False.elim (hno_rep (2 * j) (2 * i) (by omega) (by omega) heq.symm)
        · omega
    have hS_ind : G.IsIndepSet S := by
      refine ⟨hS_nd, fun u hu v hv => ?_⟩
      rcases List.mem_map.mp hu with ⟨i, hi, rfl⟩
      rcases List.mem_map.mp hv with ⟨j, hj, rfl⟩
      have him : i < m := List.mem_range.mp hi
      have hjm : j < m := List.mem_range.mp hj
      by_cases hij : i = j
      · subst hij; exact G.loopless _
      · by_cases hlt : i < j
        · exact hno_short (2 * i) (2 * j) (by omega) (by omega)
        · rw [G.symm]
          exact hno_short (2 * j) (2 * i) (by omega) (by omega)
    have hle := ha.2 S hS_ind
    have hlenS : S.length = m := by simp [S]
    omega

private theorem r10p2_countP_le_two_of_no_three (m : Nat) (P : Nat → Bool)
    (hno3 : ∀ i j k : Nat, i < j → j < k → k < m → ¬ (P i = true ∧ P j = true ∧ P k = true)) :
    (List.range m).countP P ≤ 2 := by
  let L := (List.range m).filter P
  have hlen : L.length = (List.range m).countP P := r10p2_length_filter_eq_countP P (List.range m)
  rw [← hlen]
  have hpw : L.Pairwise (· < ·) := List.pairwise_lt_range.sublist (List.filter_sublist)
  have hmem : ∀ x ∈ L, x < m ∧ P x = true := fun x hx => by
    rcases List.mem_filter.mp hx with ⟨hr, hp⟩
    exact ⟨List.mem_range.mp hr, hp⟩
  cases hL : L with
  | nil => simp
  | cons a lr1 =>
    cases lr1 with
    | nil => simp
    | cons b lr2 =>
      cases lr2 with
      | nil => simp
      | cons c _ =>
        exfalso
        rw [hL] at hpw hmem
        have hab : a < b := (List.pairwise_cons.mp hpw).1 b (by simp)
        have hbc : b < c := (List.pairwise_cons.mp (List.pairwise_cons.mp hpw).2).1 c (by simp)
        have hc := hmem c (by simp)
        exact hno3 a b c hab hbc hc.1 ⟨(hmem a (by simp)).2, (hmem b (by simp)).2, hc.2⟩

/-- **Round-10 Theorem 21e (`diam + omega ≤ n + 1`):**
    Every connected graph `G` with diameter `d` and clique number `w` satisfies
    `d + w ≤ n + 1` (any clique intersects a shortest path in at most 2 vertices). -/
theorem SimpleGraphFin.connected_diam_add_clique_le {n d w : Nat}
    (G : SimpleGraphFin n) (hd : G.DiameterNum d) (hw : G.CliqueNum w) :
    d + w ≤ n + 1 := by
  rcases hw.1 with ⟨K, hK, hKlen⟩
  have hK_le_n : K.length ≤ n := by
    rw [r10p2_nodup_length_eq_countP_finRange K hK.1]
    exact Nat.le_trans (List.countP_le_length) (by simp)
  by_cases hd0 : d = 0
  · omega
  · rcases r10p2_geodesic_exists G hd (by omega) with ⟨u0, W, hWlen, hno_rep, hno_short⟩
    let Widx := (List.range (d + 1)).map (fun i => r10p2_nthOr W i u0)
    have hWidx_nd : Widx.Nodup := by
      apply r10p2_nodup_map_inj _ (List.range (d + 1)) List.nodup_range
      intro i hi j hj heq
      have him := List.mem_range.mp hi
      have hjm := List.mem_range.mp hj
      by_cases hij : i < j
      · exact False.elim (hno_rep i j hij hjm heq)
      · by_cases hji : j < i
        · exact False.elim (hno_rep j i hji him heq.symm)
        · omega
    have hWidx_len : Widx.length = d + 1 := by simp [Widx]
    have hinter_le2 : Widx.countP (fun v => decide (v ∈ K)) ≤ 2 := by
      dsimp [Widx]
      rw [List.countP_map]
      apply r10p2_countP_le_two_of_no_three (d + 1)
      intro i j k hij hjk hkm ⟨hpi, _, hpk⟩
      simp only [Function.comp_def, decide_eq_true_eq] at hpi hpk
      have hne_ik : r10p2_nthOr W i u0 ≠ r10p2_nthOr W k u0 := hno_rep i k (by omega) hkm
      have hadj_ik : G.adj (r10p2_nthOr W i u0) (r10p2_nthOr W k u0) = true := hK.2 _ hpi _ hpk hne_ik
      have hnadj_ik := hno_short i k (by omega) hkm
      rw [hadj_ik] at hnadj_ik; cases hnadj_ik
    have hsum_ie :
        Widx.length + K.length ≤ n + Widx.countP (fun v => decide (v ∈ K)) := by
      rw [r10p2_nodup_length_eq_countP_finRange Widx hWidx_nd,
          r10p2_nodup_length_eq_countP_finRange K hK.1]
      have hinter_eq :
          Widx.countP (fun v => decide (v ∈ K)) =
          (List.finRange n).countP (fun v => decide (v ∈ Widx) && decide (v ∈ K)) := by
        rw [countP_eq_sumNat, countP_eq_sumNat]
        have h1 : sumNat Widx (fun v => if decide (v ∈ K) = true then 1 else 0) =
            sumNat Widx (fun x => sumNat (List.finRange n)
              (fun v => if v = x then (if decide (v ∈ K) = true then 1 else 0) else 0)) := by
          apply sumNat_congr; intro x _
          have hm := sumNat_const_mul (if decide (x ∈ K) = true then 1 else 0) (List.finRange n)
            (fun v => if v = x then 1 else 0)
          rw [sumNat_eq_indicator_one (List.finRange n) (List.nodup_finRange n) x (List.mem_finRange x), Nat.mul_one] at hm
          refine hm.trans (sumNat_congr _ _ _ fun v _ => ?_)
          by_cases hvx : v = x <;> simp [hvx]
        rw [h1, sumNat_swap]
        apply sumNat_congr; intro v _
        by_cases hvW : v ∈ Widx
        · have hm := sumNat_const_mul (if decide (v ∈ K) = true then 1 else 0) Widx (fun x => if x = v then 1 else 0)
          rw [sumNat_eq_indicator_one Widx hWidx_nd v hvW, Nat.mul_one] at hm
          have hsym : sumNat Widx (fun x => if v = x then (if decide (v ∈ K) = true then 1 else 0) else 0) =
              sumNat Widx (fun x => (if decide (v ∈ K) = true then 1 else 0) * (if x = v then 1 else 0)) := by
            apply sumNat_congr; intro x _; by_cases h : v = x
            · subst h; simp
            · have h' : x ≠ v := Ne.symm h; simp [h, h']
          rw [hsym, ← hm]
          simp [hvW]
        · have hz : ∀ (L : List (Fin n)), v ∉ L →
              sumNat L (fun x => if v = x then (if decide (v ∈ K) = true then 1 else 0) else 0) = 0 := by
            intro L hvL
            induction L with
            | nil => rfl
            | cons x wr ih =>
              have hvx : v ≠ x := fun h => hvL (by simp [h])
              have hvwr : v ∉ wr := fun hm => hvL (by simp [hm])
              simp only [sumNat, hvx, ↓reduceIte, Nat.zero_add]
              exact ih hvwr
          rw [hz Widx hvW]; simp [hvW]
      rw [hinter_eq]
      rw [countP_eq_sumNat, countP_eq_sumNat, countP_eq_sumNat, ← sumNat_add]
      have hn_sum : n = sumNat (List.finRange n) (fun _ => 1) := by
        have hlen : ∀ L : List (Fin n), sumNat L (fun _ => 1) = L.length := by
          intro L; induction L with | nil => rfl | cons _ lr ih => simp [sumNat, ih]; omega
        rw [hlen, List.length_finRange]
      have hbound : sumNat (List.finRange n)
          (fun x => (if decide (x ∈ Widx) = true then 1 else 0) + (if decide (x ∈ K) = true then 1 else 0)) ≤
          sumNat (List.finRange n)
          (fun x => 1 + (if (decide (x ∈ Widx) && decide (x ∈ K)) = true then 1 else 0)) := by
        apply sumNat_mono; intro v _
        by_cases h1 : v ∈ Widx <;> by_cases h2 : v ∈ K <;> simp [h1, h2] <;> omega
      rw [sumNat_add (List.finRange n) (fun _ => 1), ← hn_sum] at hbound
      exact hbound
    omega

-- ============================================================================
-- 22. Additive Set Inclusions, Symmetry Ceiling, Restricted Sumset & `3|A-A| <= 2|2A-A| + 1`
-- ============================================================================

/-- **Round-10 Theorem 22a (`dilate_sum ≤ sum3`):** `|A + 2·A| ≤ |A + A + A|`. -/
theorem intDilateSum2Card_le_intSum3Card (A : Nat → Bool) (N : Nat) :
    intDilateSum2Card A N ≤ intSum3Card A N := by
  unfold intDilateSum2Card intSum3Card
  exact countP_map_le id (fun _ _ h => h) (List.range (3 * N)) (List.range (3 * N))
    List.nodup_range List.nodup_range _ _ (fun s hs hp => by
      refine ⟨hs, ?_⟩
      rcases List.any_eq_true.mp hp with ⟨a, ha, hp2⟩
      rcases List.any_eq_true.mp hp2 with ⟨b, hb, hab⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hab
      rcases hab with ⟨⟨haA, hbA⟩, hab_eq⟩
      rw [List.any_eq_true]; refine ⟨a, ha, ?_⟩
      rw [List.any_eq_true]; refine ⟨b, hb, ?_⟩
      rw [List.any_eq_true]; refine ⟨b, hb, ?_⟩
      simp [haA, hbA]; omega)

/-- **Round-10 Theorem 22b (`dilate_diff ≤ sum2_diff1`):** `|A - 2·A| ≤ |A + A - A|`. -/
theorem intDilateDiff2Card_le_intSum2Diff1Card (A : Nat → Bool) (N : Nat) :
    intDilateDiff2Card A N ≤ intSum2Diff1Card A N := by
  by_cases hN0 : N = 0
  · subst hN0; simp [intDilateDiff2Card, intSum2Diff1Card]
  · let m := N - 1
    let P : Nat → Bool := fun s =>
      (List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a + 2 * (N - 1 - b) = s)))
    let Q : Nat → Bool := fun s =>
      (List.range N).any (fun a => (List.range N).any (fun b => (List.range N).any (fun c =>
        A a && A b && A c && decide (a + b + (N - 1) = s + c))))
    let S := (List.range (3 * N)).filter P
    have hlenP : S.length = intDilateDiff2Card A N := r10p2_length_filter_eq_countP P (List.range (3 * N))
    have hS_cnt : S.countP (fun _ => true) = S.length := by simp
    unfold intSum2Diff1Card
    change intDilateDiff2Card A N ≤ (List.range (3 * N)).countP Q
    rw [← hlenP, ← hS_cnt]
    have hS_ub : ∀ s ∈ S, s ≤ 3 * m := by
      intro s hs
      have hp := (List.mem_filter.mp hs).2
      rcases List.any_eq_true.mp hp with ⟨a, ha, hp2⟩
      rcases List.any_eq_true.mp hp2 with ⟨b, hb, hab⟩
      have haN := List.mem_range.mp ha
      have hbN := List.mem_range.mp hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hab
      rcases hab with ⟨_, hab_eq⟩
      dsimp [m]; omega
    exact countP_map_le (fun s => if s ≤ 3 * m then 3 * m - s else s + 3 * N)
      (fun x y hxy => by
        by_cases hx : x ≤ 3 * m <;> by_cases hy : y ≤ 3 * m <;> simp [hx, hy] at hxy <;> omega)
      S (List.range (3 * N)) (List.nodup_range.sublist List.filter_sublist) List.nodup_range
      (fun _ => true) Q (fun s hs _ => by
        have hsm : s ≤ 3 * m := hS_ub s hs
        simp only [hsm, ↓reduceIte]
        have hp := (List.mem_filter.mp hs).2
        rcases List.any_eq_true.mp hp with ⟨a, ha, hp2⟩
        rcases List.any_eq_true.mp hp2 with ⟨b, hb, hab⟩
        have haN := List.mem_range.mp ha
        have hbN := List.mem_range.mp hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hab
        rcases hab with ⟨⟨haA, hbA⟩, hab_eq⟩
        refine ⟨List.mem_range.mpr (by dsimp [m] at hsm ⊢; omega), ?_⟩
        dsimp [Q]
        rw [List.any_eq_true]; refine ⟨b, hb, ?_⟩
        rw [List.any_eq_true]; refine ⟨b, hb, ?_⟩
        rw [List.any_eq_true]; refine ⟨a, ha, ?_⟩
        simp [haA, hbA]; dsimp [m]; omega)

private theorem r10p2_sumNat_range_add (a b : Nat) (f : Nat → Nat) :
    sumNat (List.range (a + b)) f =
      sumNat (List.range a) f + sumNat (List.range b) (fun k => f (a + k)) := by
  induction b with
  | zero => simp [sumNat]
  | succ b ih =>
    rw [← Nat.add_assoc, List.range_succ, sumNat_append, ih, List.range_succ, sumNat_append]
    simp only [sumNat]
    omega

private theorem r10p2_sumNat_range_rev (m : Nat) (f : Nat → Nat) :
    sumNat (List.range (m + 1)) (fun x => f (m - x)) = sumNat (List.range (m + 1)) f := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have hfront : sumNat (List.range (k + 2)) (fun x => f (k + 1 - x)) =
        f (k + 1) + sumNat (List.range (k + 1)) (fun t => f (k - t)) := by
      have hr : List.range (k + 2) = 0 :: (List.range (k + 1)).map Nat.succ := List.range_succ_eq_map
      rw [hr, sumNat, sumNat_map]
      simp only [Nat.sub_zero]
      have hc : sumNat (List.range (k + 1)) (fun x => f (k + 1 - Nat.succ x)) =
          sumNat (List.range (k + 1)) (fun t => f (k - t)) := by
        apply sumNat_congr; intro x _; congr 1; omega
      rw [hc]
    rw [hfront, ih]
    have hback : List.range (k + 2) = List.range (k + 1) ++ [k + 1] := List.range_succ
    rw [hback, sumNat_append, sumNat, sumNat]
    omega

/-- **Round-10 Theorem 22c (`3 * diffset ≤ 2 * sum2_diff1 + 1`):**
    For every normalized `A ⊆ {0, ..., N-1}` (`0, N-1 ∈ A`, `1 ≤ N`),
    `3 * |A - A| ≤ 2 * |A + A - A| + 1`. -/
theorem three_diffset_le_two_sum2Diff1_add_one (A : Nat → Bool) (N : Nat)
    (hN : 1 ≤ N) (h0 : A 0 = true) (hmax : A (N - 1) = true) :
    3 * intDiffsetCard A N ≤ 2 * intSum2Diff1Card A N + 1 := by
  let m := N - 1
  have hmN : N = m + 1 := by omega
  let isD : Nat → Bool := fun s =>
    (List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a + m = s + b)))
  let isS2D : Nat → Bool := fun s =>
    (List.range N).any (fun a => (List.range N).any (fun b => (List.range N).any (fun c =>
      A a && A b && A c && decide (a + b + m = s + c))))
  let fd : Nat → Nat := fun s => if isD s then 1 else 0
  let fs : Nat → Nat := fun s => if isS2D s then 1 else 0
  have hd_eq : intDiffsetCard A N = sumNat (List.range (2 * N)) fd := by
    unfold intDiffsetCard; rw [countP_eq_sumNat]
  have hs_eq : intSum2Diff1Card A N = sumNat (List.range (3 * N)) fs := by
    unfold intSum2Diff1Card; rw [countP_eq_sumNat]
  have hd_tail0 : ∀ k, fd (2 * m + 1 + k) = 0 := by
    intro k
    dsimp [fd]
    cases h : isD (2 * m + 1 + k)
    · rfl
    · exfalso
      rcases List.any_eq_true.mp h with ⟨a, ha, hp2⟩
      rcases List.any_eq_true.mp hp2 with ⟨b, _, hab⟩
      have haN := List.mem_range.mp ha
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hab
      rcases hab with ⟨_, hab_eq⟩
      omega
  have h2N : 2 * N = (2 * m + 1) + 1 := by omega
  have hd_2m1 : intDiffsetCard A N = sumNat (List.range (2 * m + 1)) fd := by
    rw [hd_eq, h2N, List.range_succ, sumNat_append, sumNat, sumNat]
    have h0' := hd_tail0 0
    simp only [Nat.add_zero] at h0'
    omega
  have hsplit_d : sumNat (List.range (2 * m + 1)) fd =
      sumNat (List.range m) fd + fd m + sumNat (List.range m) (fun k => fd (m + 1 + k)) := by
    have heq1 : 2 * m + 1 = (m + 1) + m := by omega
    rw [heq1, r10p2_sumNat_range_add (m + 1) m fd, List.range_succ, sumNat_append, sumNat, sumNat]
    omega
  have hd_sym : sumNat (List.range m) fd = sumNat (List.range m) (fun k => fd (m + 1 + k)) := by
    cases hm_val : m with
    | zero => rfl
    | succ m' =>
      rw [← r10p2_sumNat_range_rev m' fd]
      apply sumNat_congr
      intro k hk
      have hkm : k ≤ m' := Nat.lt_succ_iff.mp (List.mem_range.mp hk)
      dsimp [fd]
      have hiff : isD (m' - k) = true ↔ isD (m' + 1 + 1 + k) = true := by
        constructor <;> intro hp
        · rcases List.any_eq_true.mp hp with ⟨a, ha, hp2⟩
          rcases List.any_eq_true.mp hp2 with ⟨b, hb, hab⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hab
          rcases hab with ⟨⟨haA, hbA⟩, hab_eq⟩
          rw [List.any_eq_true]; refine ⟨b, hb, ?_⟩
          rw [List.any_eq_true]; refine ⟨a, ha, ?_⟩
          simp [hbA, haA]; omega
        · rcases List.any_eq_true.mp hp with ⟨a, ha, hp2⟩
          rcases List.any_eq_true.mp hp2 with ⟨b, hb, hab⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hab
          rcases hab with ⟨⟨haA, hbA⟩, hab_eq⟩
          rw [List.any_eq_true]; refine ⟨b, hb, ?_⟩
          rw [List.any_eq_true]; refine ⟨a, ha, ?_⟩
          simp [hbA, haA]; omega
      cases h1 : isD (m' - k) <;> cases h2 : isD (m' + 1 + 1 + k) <;> simp_all
  have hfd_m_le1 : fd m ≤ 1 := by dsimp [fd]; split <;> omega
  have h3N : 3 * N = ((2 * m + 1) + m) + 2 := by omega
  have hs_lower :
      sumNat (List.range (2 * m + 1)) fs + sumNat (List.range m) (fun k => fs (2 * m + 1 + k)) ≤
      intSum2Diff1Card A N := by
    rw [hs_eq, h3N, r10p2_sumNat_range_add ((2 * m + 1) + m) 2 fs, r10p2_sumNat_range_add (2 * m + 1) m fs]
    omega
  have hp1 : sumNat (List.range (2 * m + 1)) fd ≤ sumNat (List.range (2 * m + 1)) fs := by
    apply sumNat_mono; intro s _
    dsimp [fd, fs]
    cases hd_s : isD s
    · simp
    · have hs_t : isS2D s = true := by
        rcases List.any_eq_true.mp hd_s with ⟨a, ha, hp2⟩
        rcases List.any_eq_true.mp hp2 with ⟨c, hc, hac⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hac
        rcases hac with ⟨⟨haA, hcA⟩, hac_eq⟩
        rw [List.any_eq_true]; refine ⟨a, ha, ?_⟩
        rw [List.any_eq_true]; refine ⟨0, List.mem_range.mpr hN, ?_⟩
        rw [List.any_eq_true]; refine ⟨c, hc, ?_⟩
        simp [haA, h0, hcA, hac_eq]
      simp [hs_t]
  have hp2 : sumNat (List.range m) (fun k => fd (m + 1 + k)) ≤
      sumNat (List.range m) (fun k => fs (2 * m + 1 + k)) := by
    apply sumNat_mono; intro k _
    dsimp [fd, fs]
    cases hd_k : isD (m + 1 + k)
    · simp
    · have hs_t : isS2D (2 * m + 1 + k) = true := by
        rcases List.any_eq_true.mp hd_k with ⟨a, ha, hp2⟩
        rcases List.any_eq_true.mp hp2 with ⟨c, hc, hac⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hac
        rcases hac with ⟨⟨haA, hcA⟩, hac_eq⟩
        rw [List.any_eq_true]; refine ⟨a, ha, ?_⟩
        rw [List.any_eq_true]; refine ⟨m, List.mem_range.mpr (by omega), ?_⟩
        rw [List.any_eq_true]; refine ⟨c, hc, ?_⟩
        have hm_true : A m = true := hmax
        simp [haA, hm_true, hcA]; omega
      simp [hs_t]
  omega

/-- **Round-10 Theorem 22d (`sym_defect + 4 ≤ 2 * k`):**
    For every normalized `A ⊆ {0, ..., N-1}` (`0, N-1 ∈ A`, `2 ≤ N`),
    `symDefectPrefix A N + 4 ≤ 2 * cardPrefix A N`. -/
theorem symDefectPrefix_add_four_le_two_card (A : Nat → Bool) (N : Nat)
    (hN : 2 ≤ N) (h0 : A 0 = true) (hmax : A (N - 1) = true) :
    symDefectPrefix A N + 4 ≤ 2 * cardPrefix A N := by
  let m := N - 1
  have hmN : N = m + 1 := by omega
  have hm_ge1 : 1 ≤ m := by omega
  have hm_true : A m = true := hmax
  have hcard_rev : sumNat (List.range (m + 1)) (fun x => if A (m - x) then 1 else 0) = cardPrefix A N := by
    rw [r10p2_sumNat_range_rev m (fun x => if A x then 1 else 0), ← hmN]
    rfl
  have hcard_id : sumNat (List.range (m + 1)) (fun x => if A x then 1 else 0) = cardPrefix A N := by
    rw [← hmN]; rfl
  have hsym_eq : symDefectPrefix A N =
      sumNat (List.range (m + 1)) (fun x => if A x != A (m - x) then 1 else 0) := by
    unfold symDefectPrefix
    rw [hmN]
    apply sumNat_congr; intro x _
    have : m + 1 - 1 - x = m - x := by omega
    rw [this]
  have hsplit : ∀ g : Nat → Nat,
      sumNat (List.range (m + 1)) g = g 0 + sumNat (List.range (m - 1)) (fun t => g (1 + t)) + g m := by
    intro g
    have hm_eq : m + 1 = (1 + (m - 1)) + 1 := by omega
    rw [hm_eq, List.range_succ, sumNat_append, r10p2_sumNat_range_add 1 (m - 1) g]
    have hr1 : List.range 1 = [0] := rfl
    rw [hr1]
    simp only [sumNat]
    have hlast : 1 + (m - 1) = m := by omega
    rw [hlast]
    omega
  have hmid_le :
      sumNat (List.range (m - 1)) (fun t => if A (1 + t) != A (m - (1 + t)) then 1 else 0) ≤
      sumNat (List.range (m - 1)) (fun t => (if A (1 + t) then 1 else 0) + (if A (m - (1 + t)) then 1 else 0)) := by
    apply sumNat_mono; intro t _
    cases A (1 + t) <;> cases A (m - (1 + t)) <;> simp
  have h2card : 2 * cardPrefix A N =
      sumNat (List.range (m + 1)) (fun x => (if A x then 1 else 0) + (if A (m - x) then 1 else 0)) := by
    rw [sumNat_add, hcard_id, hcard_rev]; omega
  rw [hsym_eq, h2card, hsplit, hsplit]
  simp only [Nat.sub_zero, Nat.sub_self, h0, hm_true, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  omega

/-- **Round-10 Theorem 22e (`2 * k ≤ rest_sum + 3`):**
    For every normalized `A ⊆ {0, ..., N-1}` (`0, N-1 ∈ A`, `2 ≤ N`),
    `2 * cardPrefix A N ≤ intRestSumCard A N + 3`. -/
theorem two_card_le_intRestSumCard_add_three (A : Nat → Bool) (N : Nat)
    (hN : 2 ≤ N) (h0 : A 0 = true) (hmax : A (N - 1) = true) :
    2 * cardPrefix A N ≤ intRestSumCard A N + 3 := by
  let m := N - 1
  have hmN : N = m + 1 := by omega
  have hm_true : A m = true := hmax
  let isR : Nat → Bool := fun s =>
    (List.range N).any (fun a => (List.range N).any (fun b => A a && A b && decide (a < b) && decide (a + b = s)))
  let fr : Nat → Nat := fun s => if isR s then 1 else 0
  have hr_eq : intRestSumCard A N = sumNat (List.range (2 * N)) fr := by
    unfold intRestSumCard; rw [countP_eq_sumNat]
  have h2N : 2 * N = (((1 + (m - 1)) + 1) + (m - 1)) + 2 := by omega
  have hr_lower :
      sumNat (List.range (m - 1)) (fun t => fr (1 + t)) + fr m +
      sumNat (List.range (m - 1)) (fun t => fr (m + 1 + t)) ≤ intRestSumCard A N := by
    rw [hr_eq, h2N,
        r10p2_sumNat_range_add (((1 + (m - 1)) + 1) + (m - 1)) 2 fr,
        r10p2_sumNat_range_add ((1 + (m - 1)) + 1) (m - 1) fr,
        List.range_succ, sumNat_append,
        r10p2_sumNat_range_add 1 (m - 1) fr]
    have h1m : 1 + (m - 1) = m := by omega
    simp only [h1m, sumNat]
    omega
  have hmid_card : cardPrefix A N = 2 + sumNat (List.range (m - 1)) (fun t => if A (1 + t) then 1 else 0) := by
    unfold cardPrefix
    have hm1 : N = (1 + (m - 1)) + 1 := by omega
    rw [hm1, List.range_succ, sumNat_append, r10p2_sumNat_range_add 1 (m - 1)]
    have hr1 : List.range 1 = [0] := rfl
    have h1m : 1 + (m - 1) = m := by omega
    rw [hr1, h1m]
    simp only [sumNat, h0, hm_true, ↓reduceIte]
    omega
  have hfr_m : fr m = 1 := by
    dsimp [fr]
    have ht : isR m = true := by
      rw [List.any_eq_true]; refine ⟨0, List.mem_range.mpr (by omega), ?_⟩
      rw [List.any_eq_true]; refine ⟨m, List.mem_range.mpr (by omega), ?_⟩
      simp [h0, hm_true]; omega
    simp [ht]
  have hlo : sumNat (List.range (m - 1)) (fun t => if A (1 + t) then 1 else 0) ≤
      sumNat (List.range (m - 1)) (fun t => fr (1 + t)) := by
    apply sumNat_mono; intro t ht
    have htm := List.mem_range.mp ht
    cases hat : A (1 + t)
    · simp
    · dsimp [fr]
      have hir : isR (1 + t) = true := by
        rw [List.any_eq_true]; refine ⟨0, List.mem_range.mpr (by omega), ?_⟩
        rw [List.any_eq_true]; refine ⟨1 + t, List.mem_range.mpr (by omega), ?_⟩
        simp [h0, hat]; omega
      simp [hir]
  have hhi : sumNat (List.range (m - 1)) (fun t => if A (1 + t) then 1 else 0) ≤
      sumNat (List.range (m - 1)) (fun t => fr (m + 1 + t)) := by
    apply sumNat_mono; intro t ht
    have htm := List.mem_range.mp ht
    cases hat : A (1 + t)
    · simp
    · dsimp [fr]
      have hir : isR (m + 1 + t) = true := by
        rw [List.any_eq_true]; refine ⟨1 + t, List.mem_range.mpr (by omega), ?_⟩
        rw [List.any_eq_true]; refine ⟨m, List.mem_range.mpr (by omega), ?_⟩
        simp [hat, hm_true]; omega
      simp [hir]
  omega

-- ============================================================================
-- 23. Erdős-Szekeres (`n <= lis * lds`), Involution `lis <= cyc` & `Av(321)` `cyc <= lis`
-- ============================================================================

private def r10p2_chainStep {n : Nat} (cmp : Nat → Nat → Bool) (p : PermFin n)
    (tbl : List (Fin n × List (Fin n))) (cur : Fin n) : List (Fin n × List (Fin n)) :=
  let prev := tbl.foldl (fun best item =>
    if cmp (p.toFun item.1).val (p.toFun cur).val && decide (best.length < item.2.length) then item.2
    else best) []
  (cur, prev ++ [cur]) :: tbl

private def r10p2_chainTbl {n : Nat} (cmp : Nat → Nat → Bool) (p : PermFin n) :
    Nat → List (Fin n × List (Fin n))
  | 0 => []
  | m + 1 =>
    let tbl := r10p2_chainTbl cmp p m
    if hm : m < n then r10p2_chainStep cmp p tbl ⟨m, hm⟩ else tbl

private theorem r10p2_foldl_best_spec {n : Nat} (cmp : Nat → Nat → Bool) (p : PermFin n)
    (cur : Fin n) (P : List (Fin n) → Prop)
    (tbl : List (Fin n × List (Fin n))) (init : List (Fin n)) (hinit : P init)
    (htbl : ∀ item ∈ tbl, cmp (p.toFun item.1).val (p.toFun cur).val = true → P item.2) :
    let res := tbl.foldl (fun best item =>
      if cmp (p.toFun item.1).val (p.toFun cur).val && decide (best.length < item.2.length) then item.2
      else best) init
    P res ∧ ∀ item ∈ tbl, cmp (p.toFun item.1).val (p.toFun cur).val = true →
      item.2.length ≤ res.length := by
  induction tbl generalizing init with
  | nil => exact ⟨hinit, fun _ h => by simp at h⟩
  | cons hd tl ih =>
    let stepFn : List (Fin n) → Fin n × List (Fin n) → List (Fin n) := fun best item =>
      if cmp (p.toFun item.1).val (p.toFun cur).val && decide (best.length < item.2.length) then item.2
      else best
    let next := stepFn init hd
    have hP_next : P next := by
      dsimp [next, stepFn]
      by_cases hc : cmp (p.toFun hd.1).val (p.toFun cur).val = true
      · by_cases hl : init.length < hd.2.length
        · simp [hc, hl]; exact htbl hd (by simp) hc
        · simp [hc, hl]; exact hinit
      · simp [hc]; exact hinit
    rcases ih next hP_next (fun it hit => htbl it (by simp [hit])) with ⟨hPres, hmax_tl⟩
    have hres_ge_next : ∀ (acc : List (Fin n)), acc.length ≤ (List.foldl stepFn acc tl).length := by
      clear ih hPres hmax_tl hP_next htbl hinit next
      intro acc
      induction tl generalizing acc with
      | nil => exact Nat.le_refl _
      | cons x xr ihx =>
        simp only [List.foldl_cons]
        refine Nat.le_trans ?_ (ihx (stepFn acc x))
        dsimp [stepFn]
        by_cases hc : (cmp (p.toFun x.1).val (p.toFun cur).val && decide (acc.length < x.2.length)) = true
        · simp only [hc, ↓reduceIte]
          rcases Bool.and_eq_true _ _ |>.mp hc with ⟨_, hl⟩
          have := of_decide_eq_true hl; omega
        · simp [hc]
    refine ⟨hPres, fun it hit hcmp => ?_⟩
    rcases List.mem_cons.mp hit with rfl | hit_tl
    · have hhd_le : it.2.length ≤ next.length := by
        dsimp [next, stepFn]
        by_cases hl : init.length < it.2.length <;> simp [hcmp, hl] <;> omega
      exact Nat.le_trans hhd_le (hres_ge_next next)
    · exact hmax_tl it hit_tl hcmp

private def r10p2_GoodItem {n : Nat} (cmp : Nat → Nat → Bool) (p : PermFin n) (m : Nat)
    (item : Fin n × List (Fin n)) : Prop :=
  item.1.val < m ∧
  1 ≤ item.2.length ∧
  (∀ u ∈ item.2, u.val ≤ item.1.val ∧ (u = item.1 ∨ cmp (p.toFun u).val (p.toFun item.1).val = true)) ∧
  item.2.Pairwise (fun u v => u.val < v.val ∧ cmp (p.toFun u).val (p.toFun v).val = true)

private theorem r10p2_chainTbl_good {n : Nat} (cmp : Nat → Nat → Bool)
    (htrans : ∀ x y z, cmp x y = true → cmp y z = true → cmp x z = true)
    (p : PermFin n) :
    ∀ m : Nat, ∀ item ∈ r10p2_chainTbl cmp p m, r10p2_GoodItem cmp p m item := by
  intro m
  induction m with
  | zero => intro _ h; simp [r10p2_chainTbl] at h
  | succ k ih =>
    intro item hmem
    simp only [r10p2_chainTbl] at hmem
    by_cases hk : k < n
    · simp only [hk, ↓reduceDIte, r10p2_chainStep, List.mem_cons] at hmem
      rcases hmem with rfl | hprev_mem
      · let cur : Fin n := ⟨k, hk⟩
        let P : List (Fin n) → Prop := fun L =>
          (∀ u ∈ L, u.val < k ∧ cmp (p.toFun u).val (p.toFun cur).val = true) ∧
          L.Pairwise (fun u v => u.val < v.val ∧ cmp (p.toFun u).val (p.toFun v).val = true)
        have hbest := (r10p2_foldl_best_spec cmp p cur P (r10p2_chainTbl cmp p k) []
          ⟨fun _ h => by simp at h, .nil⟩
          (fun it hit hcmp => by
            obtain ⟨hit_lt, _, hit_u, hit_pw⟩ := ih it hit
            refine ⟨fun u hu => ?_, hit_pw⟩
            obtain ⟨hu_le, hu_eq_or⟩ := hit_u u hu
            refine ⟨by omega, ?_⟩
            rcases hu_eq_or with rfl | huc
            · exact hcmp
            · exact htrans _ _ _ huc hcmp)).1
        refine ⟨by simp, by simp, ?_, ?_⟩
        · intro u hu
          rcases List.mem_append.mp hu with hu_p | hu_c
          · obtain ⟨hu_lt, hu_cmp⟩ := hbest.1 u hu_p
            exact ⟨by dsimp [cur]; omega, Or.inr hu_cmp⟩
          · simp only [List.mem_singleton] at hu_c
            subst hu_c
            exact ⟨Nat.le_refl _, Or.inl rfl⟩
        · rw [List.pairwise_append]
          refine ⟨hbest.2, List.pairwise_singleton _ _, ?_⟩
          intro u hu v hv
          simp only [List.mem_singleton] at hv
          subst hv
          exact hbest.1 u hu
      · obtain ⟨h1, h2, h3, h4⟩ := ih item hprev_mem
        exact ⟨by omega, h2, h3, h4⟩
    · simp only [hk, ↓reduceDIte] at hmem
      obtain ⟨h1, h2, h3, h4⟩ := ih item hmem
      exact ⟨by omega, h2, h3, h4⟩

private theorem r10p2_chainTbl_mem_mono {n : Nat} (cmp : Nat → Nat → Bool) (p : PermFin n)
    {a b : Nat} (hab : a ≤ b) {item : Fin n × List (Fin n)}
    (hm : item ∈ r10p2_chainTbl cmp p a) : item ∈ r10p2_chainTbl cmp p b := by
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0; exact hm
  | succ k ih =>
    by_cases hak : a ≤ k
    · have ihk := ih hak
      simp only [r10p2_chainTbl]
      by_cases hk : k < n
      · simp [hk, r10p2_chainStep, ihk]
      · simp [hk, ihk]
    · have ha_eq : a = k + 1 := by omega
      subst ha_eq; exact hm

private def r10p2_chainAt {n : Nat} (cmp : Nat → Nat → Bool) (p : PermFin n) (i : Fin n) : List (Fin n) :=
  match r10p2_chainTbl cmp p (i.val + 1) with
  | (_, ch) :: _ => ch
  | [] => [i]

private theorem r10p2_chainAt_head {n : Nat} (cmp : Nat → Nat → Bool) (p : PermFin n) (i : Fin n) :
    (i, r10p2_chainAt cmp p i) ∈ r10p2_chainTbl cmp p (i.val + 1) ∧
    (∀ j : Fin n, j.val < i.val → cmp (p.toFun j).val (p.toFun i).val = true →
      (r10p2_chainAt cmp p j).length + 1 ≤ (r10p2_chainAt cmp p i).length) := by
  have hi : i.val < n := i.isLt
  have hcur_eq : (⟨i.val, hi⟩ : Fin n) = i := Fin.ext rfl
  have htbl_eq : r10p2_chainTbl cmp p (i.val + 1) = r10p2_chainStep cmp p (r10p2_chainTbl cmp p i.val) i := by
    simp [r10p2_chainTbl, hi, hcur_eq]
  have hch_eq : r10p2_chainAt cmp p i =
      ((r10p2_chainTbl cmp p i.val).foldl (fun best item =>
        if cmp (p.toFun item.1).val (p.toFun i).val && decide (best.length < item.2.length) then item.2
        else best) []) ++ [i] := by
    unfold r10p2_chainAt
    rw [htbl_eq]
    rfl
  refine ⟨by rw [htbl_eq, hch_eq]; simp [r10p2_chainStep], ?_⟩
  intro j hji hcmp
  have hj_mem_own : (j, r10p2_chainAt cmp p j) ∈ r10p2_chainTbl cmp p (j.val + 1) := by
    have hj_lt : j.val < n := j.isLt
    have hj_eq : (⟨j.val, hj_lt⟩ : Fin n) = j := Fin.ext rfl
    have ht : r10p2_chainTbl cmp p (j.val + 1) = r10p2_chainStep cmp p (r10p2_chainTbl cmp p j.val) j := by
      simp [r10p2_chainTbl, hj_lt, hj_eq]
    unfold r10p2_chainAt
    rw [ht]; simp [r10p2_chainStep]
  have hj_in_i : (j, r10p2_chainAt cmp p j) ∈ r10p2_chainTbl cmp p i.val :=
    r10p2_chainTbl_mem_mono cmp p (by omega : j.val + 1 ≤ i.val) hj_mem_own
  have hmax := (r10p2_foldl_best_spec cmp p i (fun _ => True) (r10p2_chainTbl cmp p i.val) []
    trivial (fun _ _ _ => trivial)).2 (j, r10p2_chainAt cmp p j) hj_in_i hcmp
  dsimp only at hmax
  rw [hch_eq, List.length_append, List.length_singleton]
  omega

private theorem r10p2_pw_lt_sublist_range :
    ∀ (k : Nat) (M : List Nat), M.Pairwise (· < ·) → (∀ x ∈ M, x < k) → M.Sublist (List.range k)
  | 0, M, _, hlt => by
    cases M with
    | nil => exact .slnil
    | cons x _ => exfalso; have := hlt x (by simp); omega
  | k + 1, M, hM, hlt => by
    rw [List.range_succ]
    by_cases hlast : k ∈ M
    · have hsplit : ∃ M0, M = M0 ++ [k] ∧ M0.Pairwise (· < ·) ∧ (∀ x ∈ M0, x < k) := by
        induction M with
        | nil => simp at hlast
        | cons a mr ihm =>
          have hMa := List.pairwise_cons.mp hM
          rcases List.mem_cons.mp hlast with heq | hmr
          · cases mr with
            | nil => subst heq; exact ⟨[], rfl, .nil, fun _ h => by simp at h⟩
            | cons b _ =>
              have hab : a < b := hMa.1 b (by simp)
              have hb : b < k + 1 := hlt b (by simp)
              omega
          · rcases ihm hMa.2 (fun x hx => hlt x (by simp [hx])) hmr with ⟨M0, heq, hpw0, hlt0⟩
            refine ⟨a :: M0, by simp [heq], .cons (fun z hz => hMa.1 z (by rw [heq]; simp [hz])) hpw0, ?_⟩
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx0
            · exact hMa.1 k hmr
            · exact hlt0 x hx0
      rcases hsplit with ⟨M0, rfl, hpw0, hlt0⟩
      exact List.Sublist.append (r10p2_pw_lt_sublist_range k M0 hpw0 hlt0) (List.Sublist.refl [k])
    · have hlt' : ∀ x ∈ M, x < k := fun x hx => by
        have h1 := hlt x hx
        have hne : x ≠ k := fun heq => hlast (heq ▸ hx)
        omega
      exact List.Sublist.trans (r10p2_pw_lt_sublist_range k M hM hlt') (List.sublist_append_left _ _)

private theorem r10p2_pairwise_lt_sublist_finRange {n : Nat} :
    ∀ (L : List (Fin n)), L.Pairwise (fun u v => u.val < v.val) → L.Sublist (List.finRange n) := by
  intro L hpw
  have hsub_range : (L.map Fin.val).Sublist (List.range n) :=
    r10p2_pw_lt_sublist_range n (L.map Fin.val) (List.pairwise_map.mpr hpw)
      (fun x hx => by rcases List.mem_map.mp hx with ⟨u, _, rfl⟩; exact u.isLt)
  rw [← finRange_map_val n] at hsub_range
  rcases r10p2_sublist_map_witness Fin.val hsub_range with ⟨xs, hxs_sub, hxs_map⟩
  have heq_xs : xs = L := by
    clear hxs_sub hsub_range hpw
    induction xs generalizing L with
    | nil =>
      cases L with
      | nil => rfl
      | cons _ _ => simp at hxs_map
    | cons x xr ih =>
      cases L with
      | nil => simp at hxs_map
      | cons y yr =>
        simp only [List.map_cons, List.cons.injEq] at hxs_map
        rw [Fin.ext hxs_map.1, ih yr hxs_map.2]
  exact heq_xs ▸ hxs_sub

/-- **Round-10 Theorem 23a (Erdős-Szekeres Monotone Subsequence Theorem, 1935):**
    For every permutation `p : PermFin n`, if every strictly increasing subsequence has length `≤ a`
    and every strictly decreasing subsequence has length `≤ b`, then `n ≤ a * b`. -/
theorem PermFin.erdos_szekeres {n : Nat} (p : PermFin n) (a b : Nat)
    (hinc : ∀ s, StrictIncSubseq s p.toList → s.length ≤ a)
    (hdec : ∀ s, p.StrictDecSubseq s → s.length ≤ b) :
    n ≤ a * b := by
  let cmpLt : Nat → Nat → Bool := fun x y => decide (x < y)
  let cmpGt : Nat → Nat → Bool := fun x y => decide (x > y)
  let incCh : Fin n → List (Fin n) := r10p2_chainAt cmpLt p
  let decCh : Fin n → List (Fin n) := r10p2_chainAt cmpGt p
  have hinc_good : ∀ i : Fin n, r10p2_GoodItem cmpLt p (i.val + 1) (i, incCh i) := fun i =>
    r10p2_chainTbl_good cmpLt (fun x y z h1 h2 => by
      simp only [cmpLt, decide_eq_true_eq] at h1 h2 ⊢; omega) p (i.val + 1) _ (r10p2_chainAt_head cmpLt p i).1
  have hdec_good : ∀ i : Fin n, r10p2_GoodItem cmpGt p (i.val + 1) (i, decCh i) := fun i =>
    r10p2_chainTbl_good cmpGt (fun x y z h1 h2 => by
      simp only [cmpGt, decide_eq_true_eq] at h1 h2 ⊢; omega) p (i.val + 1) _ (r10p2_chainAt_head cmpGt p i).1
  have hinc_bound : ∀ i : Fin n, 1 ≤ (incCh i).length ∧ (incCh i).length ≤ a := by
    intro i
    obtain ⟨_, hge1, _, hpw⟩ := hinc_good i
    have hsub_fin : (incCh i).Sublist (List.finRange n) :=
      r10p2_pairwise_lt_sublist_finRange (incCh i) (hpw.imp (fun h => h.1))
    let vals := (incCh i).map (fun u => (p.toFun u).val)
    have hsub_to : vals.Sublist p.toList := hsub_fin.map _
    have hpw_vals : vals.Pairwise (· < ·) := by
      rw [List.pairwise_map]
      exact hpw.imp (fun h => of_decide_eq_true h.2)
    have hle := hinc vals ⟨hsub_to, hpw_vals⟩
    simpa [vals] using And.intro hge1 hle
  have hdec_bound : ∀ i : Fin n, 1 ≤ (decCh i).length ∧ (decCh i).length ≤ b := by
    intro i
    obtain ⟨_, hge1, _, hpw⟩ := hdec_good i
    have hsub_fin : (decCh i).Sublist (List.finRange n) :=
      r10p2_pairwise_lt_sublist_finRange (decCh i) (hpw.imp (fun h => h.1))
    let vals := (decCh i).map (fun u => (p.toFun u).val)
    have hsub_to : vals.Sublist p.toList := hsub_fin.map _
    have hpw_vals : vals.Pairwise (· > ·) := by
      rw [List.pairwise_map]
      exact hpw.imp (fun h => of_decide_eq_true h.2)
    have hle := hdec vals ⟨hsub_to, hpw_vals⟩
    simpa [vals] using And.intro hge1 hle
  let code : Fin n → Nat := fun i => ((incCh i).length - 1) * b + ((decCh i).length - 1)
  have hcode_lt : ∀ i : Fin n, code i < a * b := by
    intro i
    obtain ⟨hi1, hia⟩ := hinc_bound i
    obtain ⟨hd1, hdb⟩ := hdec_bound i
    have ha_pos : 1 ≤ a := by omega
    have hb_pos : 1 ≤ b := by omega
    dsimp [code]
    have hmul : ((incCh i).length - 1) * b ≤ (a - 1) * b := Nat.mul_le_mul_right b (by omega)
    have hsplit_ab : (a - 1) * b + b = a * b := by
      have h1 := Nat.add_mul (a - 1) 1 b
      have ha1 : a - 1 + 1 = a := by omega
      rw [ha1, Nat.one_mul] at h1
      exact h1.symm
    omega
  have hstep_pair : ∀ j i : Fin n, j.val < i.val →
      (incCh j).length ≠ (incCh i).length ∨ (decCh j).length ≠ (decCh i).length := by
    intro j i hji
    have hne_p : (p.toFun j).val ≠ (p.toFun i).val := fun hv => by
      have := p.toFun_inj (Fin.ext hv)
      rw [this] at hji; omega
    by_cases hlt : (p.toFun j).val < (p.toFun i).val
    · left
      have hstep := (r10p2_chainAt_head cmpLt p i).2 j hji (decide_eq_true hlt)
      change (incCh j).length + 1 ≤ (incCh i).length at hstep
      omega
    · right
      have hgt : (p.toFun j).val > (p.toFun i).val := by omega
      have hstep := (r10p2_chainAt_head cmpGt p i).2 j hji (decide_eq_true hgt)
      change (decCh j).length + 1 ≤ (decCh i).length at hstep
      omega
  have hcnt_F : (List.finRange n).countP (fun _ => true) = n := by simp
  have hcnt_R : (List.range (a * b)).countP (fun _ => true) = a * b := by simp
  rw [← hcnt_F, ← hcnt_R]
  exact countP_map_le code (fun u v huv => by
    obtain ⟨hu1, _⟩ := hinc_bound u
    obtain ⟨hv1, _⟩ := hinc_bound v
    obtain ⟨hdu1, hdub⟩ := hdec_bound u
    obtain ⟨hdv1, hdvb⟩ := hdec_bound v
    dsimp [code] at huv
    have hdiv_mod : (incCh u).length - 1 = (incCh v).length - 1 ∧
        (decCh u).length - 1 = (decCh v).length - 1 := by
      have hy1 : (decCh u).length - 1 < b := by omega
      have hy2 : (decCh v).length - 1 < b := by omega
      by_cases hx_lt : (incCh u).length - 1 < (incCh v).length - 1
      · have hle : ((incCh u).length - 1 + 1) * b ≤ ((incCh v).length - 1) * b :=
          Nat.mul_le_mul_right b (by omega)
        rw [Nat.add_mul, Nat.one_mul] at hle
        omega
      · by_cases hx_gt : (incCh v).length - 1 < (incCh u).length - 1
        · have hle : ((incCh v).length - 1 + 1) * b ≤ ((incCh u).length - 1) * b :=
          Nat.mul_le_mul_right b (by omega)
          rw [Nat.add_mul, Nat.one_mul] at hle
          omega
        · have hxeq : (incCh u).length - 1 = (incCh v).length - 1 := by omega
          rw [hxeq] at huv
          exact ⟨hxeq, by omega⟩
    have hinc_eq : (incCh u).length = (incCh v).length := by omega
    have hdec_eq : (decCh u).length = (decCh v).length := by omega
    by_cases huv_lt : u.val < v.val
    · rcases hstep_pair u v huv_lt with h1 | h2
      · exact absurd hinc_eq h1
      · exact absurd hdec_eq h2
    · by_cases hvu_lt : v.val < u.val
      · rcases hstep_pair v u hvu_lt with h1 | h2
        · exact absurd hinc_eq.symm h1
        · exact absurd hdec_eq.symm h2
      · exact Fin.ext (by omega))
    (List.finRange n) (List.range (a * b)) (List.nodup_finRange n) List.nodup_range
    (fun _ => true) (fun _ => true) (fun i _ _ => ⟨List.mem_range.mpr (hcode_lt i), rfl⟩)

private theorem r10p2_involution_iter_two {n : Nat} (p : PermFin n) (hinv : p.IsInvolution)
    (u : Fin n) : ∀ k : Nat, p.iterPerm k u = u ∨ p.iterPerm k u = p.toFun u
  | 0 => Or.inl rfl
  | k + 1 => by
    rcases r10p2_involution_iter_two p hinv u k with h | h
    · exact Or.inr (by simp [PermFin.iterPerm, h])
    · exact Or.inl (by simp [PermFin.iterPerm, h, hinv u])

/-- **Round-10 Theorem 23b (Involution LIS ≤ Cycle Count):**
    For every involution `p : PermFin n`, every strictly increasing subsequence of `p.toList`
    contains at most one entry per cycle (`s.length ≤ p.cycCnt`). -/
theorem PermFin.involution_incSubseq_le_cycCnt {n : Nat} (p : PermFin n)
    (hinv : p.IsInvolution) (s : List Nat) (hs : StrictIncSubseq s p.toList) :
    s.length ≤ p.cycCnt := by
  rcases r10p2_sublist_map_witness (fun i : Fin n => (p.toFun i).val) hs.1 with ⟨idx, hidx_sub, hidx_map⟩
  have hidx_nd : idx.Nodup := (List.nodup_finRange n).sublist hidx_sub
  have hfin_pw : (List.finRange n).Pairwise (fun u v => u.val < v.val) := by
    have hv : ((List.finRange n).map Fin.val).Pairwise (· < ·) := by
      rw [finRange_map_val]; exact List.pairwise_lt_range
    exact List.pairwise_map.mp hv
  have hidx_lt : idx.Pairwise (fun u v => u.val < v.val) := hfin_pw.sublist hidx_sub
  have hidx_val_lt : idx.Pairwise (fun u v => (p.toFun u).val < (p.toFun v).val) := by
    have hm := hs.2
    rw [← hidx_map, List.pairwise_map] at hm
    exact hm
  let rep : Fin n → Fin n := fun u => if u.val ≤ (p.toFun u).val then u else p.toFun u
  have hrep_min : ∀ u : Fin n, p.isCycleMin (rep u) = true := by
    intro u
    unfold PermFin.isCycleMin
    rw [List.all_eq_true]
    intro k _
    simp only [decide_eq_true_eq]
    dsimp [rep]
    by_cases hle : u.val ≤ (p.toFun u).val
    · simp only [hle, ↓reduceIte]
      rcases r10p2_involution_iter_two p hinv u k with h | h <;> rw [h] <;> omega
    · simp only [hle, ↓reduceIte]
      rcases r10p2_involution_iter_two p hinv (p.toFun u) k with h | h
      · rw [h]; exact Nat.le_refl _
      · rw [h, hinv u]; omega
  let idxSub : List {u : Fin n // u ∈ idx} := idx.attach
  have hSub_nd : idxSub.Nodup := by
    suffices ∀ L : List (Fin n), L.Nodup → L.attach.Nodup from this idx hidx_nd
    intro L hL
    rw [List.attach]
    let rec go (M : List (Fin n)) (hsub : ∀ x ∈ M, x ∈ L) (hM : M.Nodup) :
        (M.pmap Subtype.mk hsub).Nodup := by
      cases M with
      | nil => simp
      | cons a mr =>
        rw [List.nodup_cons] at hM
        simp only [List.pmap, List.nodup_cons, List.mem_pmap]
        refine ⟨?_, go mr (fun x hx => hsub x (by simp [hx])) hM.2⟩
        rintro ⟨b, hbm, heq⟩
        injection heq with hab
        exact hM.1 (hab ▸ hbm)
    exact go L (fun _ h => h) hL
  have hpair_symm : ∀ u v : Fin n, u ∈ idx → v ∈ idx → u.val < v.val → (p.toFun u).val < (p.toFun v).val := by
    clear idxSub hSub_nd hidx_sub hidx_map hs
    induction idx with
    | nil => intro _ _ h; simp at h
    | cons a ir ih =>
      have h1 := List.pairwise_cons.mp hidx_lt
      have h2 := List.pairwise_cons.mp hidx_val_lt
      have hnd' := List.nodup_cons.mp hidx_nd
      intro u v hu hv huv
      rcases List.mem_cons.mp hu with rfl | hu_ir
      · rcases List.mem_cons.mp hv with rfl | hv_ir
        · omega
        · exact h2.1 v hv_ir
      · rcases List.mem_cons.mp hv with rfl | hv_ir
        · have := h1.1 u hu_ir; omega
        · exact ih hnd'.2 h1.2 h2.2 u v hu_ir hv_ir huv
  have hrep_inj : ∀ a b : {u : Fin n // u ∈ idx}, rep a.1 = rep b.1 → a = b := by
    intro ⟨u, hu⟩ ⟨v, hv⟩ heq
    suffices u = v from Subtype.ext this
    have hu_cases : rep u = u ∨ rep u = p.toFun u := by
      dsimp [rep]; by_cases h : u.val ≤ (p.toFun u).val <;> simp [h]
    have hv_cases : rep v = v ∨ rep v = p.toFun v := by
      dsimp [rep]; by_cases h : v.val ≤ (p.toFun v).val <;> simp [h]
    have hor : u = v ∨ v = p.toFun u := by
      rcases hu_cases with h1 | h1 <;> rcases hv_cases with h2 | h2
      · exact Or.inl (h1 ▸ h2 ▸ heq)
      · have : u = p.toFun v := h1 ▸ h2 ▸ heq
        exact Or.inr (by rw [this, hinv v])
      · exact Or.inr (h1 ▸ h2 ▸ heq).symm
      · exact Or.inl (p.toFun_inj (h1 ▸ h2 ▸ heq))
    rcases hor with h | h
    · exact h
    · by_cases hlt : u.val < v.val
      · have hp_lt := hpair_symm u v hu hv hlt
        have hpv : p.toFun v = u := by rw [h, hinv u]
        rw [← h, hpv] at hp_lt
        omega
      · by_cases hgt : v.val < u.val
        · have hp_lt := hpair_symm v u hv hu hgt
          have hpv : p.toFun v = u := by rw [h, hinv u]
          rw [hpv, ← h] at hp_lt
          omega
        · exact Fin.ext (by omega)
  have hlen_eq : s.length = idxSub.countP (fun _ => true) := by
    simp [idxSub, ← hidx_map]
  rw [hlen_eq]
  unfold PermFin.cycCnt
  exact countP_map_le (fun x => rep x.1) hrep_inj idxSub (List.finRange n) hSub_nd
    (List.nodup_finRange n) (fun _ => true) p.isCycleMin
    (fun x _ _ => ⟨List.mem_finRange _, hrep_min x.1⟩)

/-- **Round-10 Theorem 23c (Involution Erdős-Szekeres Cycle Bound `n ≤ cyc * lds`):**
    For every involution `p : PermFin n`, if every strictly decreasing subsequence has length `≤ b`,
    then `n ≤ p.cycCnt * b` (proving Round-9 survivor `r9_P_INV_es_n+0<=cyc*lds` universally). -/
theorem PermFin.involution_erdos_szekeres_cyc {n : Nat} (p : PermFin n) (b : Nat)
    (hinv : p.IsInvolution) (hdec : ∀ s, p.StrictDecSubseq s → s.length ≤ b) :
    n ≤ p.cycCnt * b :=
  p.erdos_szekeres p.cycCnt b (fun s hs => p.involution_incSubseq_le_cycCnt hinv s hs) hdec

/-- **Round-10 Theorem 23d (`Av(321)` Cycle Count ≤ LIS):**
    Every `321`-avoiding permutation `p : PermFin n` admits a strictly increasing subsequence
    of `p.toList` of length at least `p.cycCnt` (proving `r5_P_AV321_1cyc<=1lis+0` universally). -/
theorem PermFin.avoids321_cycCnt_le_lis {n : Nat} (p : PermFin n) (h321 : p.Avoids321) :
    ∃ sub : List Nat, StrictIncSubseq sub p.toList ∧ p.cycCnt ≤ sub.length := by
  by_cases hn2 : 2 ≤ n
  · let C := (List.finRange n).filter p.isCycleMin
    let sub := C.map (fun i => (p.toFun i).val)
    have hC_len : C.length = p.cycCnt := r10p2_length_filter_eq_countP p.isCycleMin (List.finRange n)
    have hC_sub : C.Sublist (List.finRange n) := List.filter_sublist
    have hfin_pw : (List.finRange n).Pairwise (fun u v => u.val < v.val) := by
      have hv : ((List.finRange n).map Fin.val).Pairwise (· < ·) := by
        rw [finRange_map_val]; exact List.pairwise_lt_range
      exact List.pairwise_map.mp hv
    have hC_pw : C.Pairwise (fun u v => u.val < v.val) := hfin_pw.sublist hC_sub
    have hC_lrmax : ∀ i ∈ C, p.IsLeftToRightMax i := by
      intro i hi
      have hmin : p.isCycleMin i = true := (List.mem_filter.mp hi).2
      unfold PermFin.isCycleMin at hmin
      have hk1 := List.all_eq_true.mp hmin 1 (List.mem_range.mpr hn2)
      simp only [PermFin.iterPerm] at hk1
      have hwexc : i.val ≤ (p.toFun i).val := of_decide_eq_true hk1
      exact (p.avoids321_wexc_iff_lrmax h321 i).mp hwexc
    have hsub_pw : sub.Pairwise (· < ·) := by
      dsimp [sub]
      rw [List.pairwise_map]
      have hgen : ∀ L : List (Fin n), L.Pairwise (fun u v => u.val < v.val) →
          (∀ i ∈ L, p.IsLeftToRightMax i) → L.Pairwise (fun u v => (p.toFun u).val < (p.toFun v).val) := by
        intro L hL hlrm
        induction L with
        | nil => exact .nil
        | cons u lr ih =>
          rw [List.pairwise_cons] at hL ⊢
          refine ⟨fun v hv => hlrm v (by simp [hv]) u (hL.1 v hv),
            ih hL.2 (fun i hi => hlrm i (by simp [hi]))⟩
      exact hgen C hC_pw hC_lrmax
    refine ⟨sub, ⟨hC_sub.map _, hsub_pw⟩, ?_⟩
    simp [sub, hC_len]
  · have hcyc_le_n : p.cycCnt ≤ n := by
      unfold PermFin.cycCnt
      exact Nat.le_trans List.countP_le_length (by simp)
    have hto_pw : p.toList.Pairwise (· < ·) := by
      cases n with
      | zero => simp [PermFin.toList]
      | succ k =>
        cases k with
        | zero =>
          have hl1 : p.toList.length = 1 := by simp [PermFin.toList]
          cases hp : p.toList with
          | nil => rw [hp] at hl1; simp at hl1
          | cons a r =>
            cases r with
            | nil => exact List.pairwise_singleton _ _
            | cons _ _ => rw [hp] at hl1; simp at hl1
        | succ _ => omega
    refine ⟨p.toList, ⟨List.Sublist.refl _, hto_pw⟩, ?_⟩
    simpa [PermFin.toList] using hcyc_le_n

end CombMining
