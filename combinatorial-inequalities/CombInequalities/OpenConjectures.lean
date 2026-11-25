import Std
import CombInequalities.CombDefs

/-!
# Featured Open Conjectures & Formalized Counterexample (`gpu-comb-mining-20261117`)

Previously open conjectures promoted into kernel-checked Lean 4 theorems in
`ProvedDiscoveries.lean` and `StatementAudit.lean`:
  - `Conj_TriangleFree_EdgeMatching` -> `SimpleGraphFin.triangleFree_edgeCount_le_matching`
  - `Conj_C4Free_MinDegMatching` -> `SimpleGraphFin.c4Free_minDeg_le_matching`
  - GPU `r2_AV231_inv_disp_lis` (`2 * inv <= disp2 + des * (des + 1)`) ->
    `PermFin.avoids231_two_inv_le_disp2_add_des`
  - `Conj_AllPerms_StackDes_Le_Peaks` (`des(S(p)) <= peaks(p)`) ->
    `PermFin.stackDes_le_peaksCnt` / `proved_Conj_AllPerms_StackDes_Le_Peaks`
  - `Conj_AllPerms_StackInv_Le_PopInv` (`inv(S(p)) <= inv(P(p))`) ->
    `PermFin.stackInv_le_popInv` / `proved_Conj_AllPerms_StackInv_Le_PopInv`
  - `Conj_Av321_TwoStackInv_Pat231` (`3 * inv(S^2(p)) <= pat_231(p)` on `Av(321)`) ->
    `PermFin.avoids321_three_stack2Inv_le_pat231` / `proved_Conj_Av321_TwoStackInv_Pat231`

Formally disproved conjectures (kernel-checked counterexamples in this file):
  - `Conj_Avoids231_InvDispLDS` (`n = 9`, `not_Conj_Avoids231_InvDispLDS`)
  - `Conj_Bipartite_Dom_IndNu_Diam` (`n = 25`, `not_Conj_Bipartite_Dom_IndNu_Diam`)

Remaining 7 open `Prop` definitions here (`6` Tier-1 novel + `1` folklore `C_4`-free bound):
  1. `Conj_C4Free_DominationMinDeg` (`2 * gamma + min_deg <= n + 1`, connected `C_4`-free `n >= 4`;
     derivable in classical literature from Ore + McCuaig-Shepherd 1989 + Reed 1996).
  2. `Conj_ModSumset_SymDefect` (`sym_defect + 2 <= |(A+A) mod N|`, normalized `N >= 5, |A| >= 3`).
  3. `Conj_ConnectedCyclic_TrA4_Zagreb2_IndC4` (`tr(A^4) + 2m <= 2 * M_2 + 8 * ind_c4`, connected cyclic).
  4. `Conj_Connected_IndepDom_Claws` (`2 * i(G) <= 2 * gamma(G) + claws(G)`, connected `n >= 5`).
  5. `Conj_IntSet_DilateSum_SymDefect` (`2 * |A| + sym_defect <= |A + 2A|`, normalized `N >= 6, |A| >= 4`).
  6. `Conj_IntSet_Dilate3Sum_SymDefect` (`3 * |A| + sym_defect <= |A + 3A| + 2`, normalized `N >= 8, |A| >= 5`).
  7. `Conj_IntSet_RestSum_SymDefect` (`|A| + sym_defect <= |A ^+ A| + 2`, normalized `N >= 6, |A| >= 4`).

Also formalized here is the kernel-checked `n = 9` counterexample proving that replacing
`n - lis = des` by `lds` in `Conj_Avoids231_InvDispLDS` is FALSE (`not_Conj_Avoids231_InvDispLDS`).

Note: Zero `sorry`, `admit`, `axiom`, `native_decide`, or `skipKernelTC`.
-/

namespace CombMining

open SimpleGraphFin
open PermFin

-- ============================================================================
-- 1. Remaining Open Conjecture Definitions
-- ============================================================================

/-- Open Formal Target 1 (Graphs): Every connected `C_4`-free graph on `n >= 4`
    vertices satisfies `2 * gamma + min_deg <= n + 1`. Fails for `C_4` (`2*2+2 = 6 > 5`)
    and attains equality on `C_5` (`2*2+2 = 6`) and `C_7` (`2*3+2 = 8`). -/
def Conj_C4Free_DominationMinDeg : Prop :=
  ∀ (n : Nat) (G : SimpleGraphFin n) (g : Nat),
    4 ≤ n → G.Connected → G.C4Free → G.DominationNum g → 2 * g + G.minDeg ≤ n + 1

/-- Open Formal Target 2 (Additive Sets): Every normalized subset `A subset {0..N-1}`
    (`0, N-1 in A`, `|A| >= 3`, `N >= 5`) satisfies `sym_defect(A) + 2 <= |(A+A) mod N|`. -/
def Conj_ModSumset_SymDefect : Prop :=
  ∀ (N : Nat) (A : Fin N → Bool) (hN : 5 ≤ N),
    (∃ h0 : 0 < N, A ⟨0, h0⟩ = true) →
    A ⟨N - 1, by omega⟩ = true →
    3 ≤ (List.finRange N).countP A →
    symDefectFin N A + 2 ≤ modSumsetCard N A

-- ============================================================================
-- 2. Concrete Boundary & Sharpness Checks (`decide`-verified)
-- ============================================================================

def cycleGraph (n : Nat) : SimpleGraphFin n where
  adj u v := decide (u ≠ v ∧ ((u.val + 1) % n = v.val ∨ (v.val + 1) % n = u.val))
  symm u v := by
    by_cases huv : u = v
    · subst huv; simp
    · simp only [ne_eq, decide_eq_decide]
      constructor
      · intro ⟨hne, h⟩; exact ⟨fun h' => hne h'.symm, h.symm⟩
      · intro ⟨hne, h⟩; exact ⟨fun h' => hne h'.symm, h.symm⟩
  loopless u := by simp

theorem cycle5_minDeg_eq_2 : (cycleGraph 5).minDeg = 2 := by decide
theorem cycle5_c4_witness : (cycleGraph 5).adj ⟨0, by omega⟩ ⟨1, by omega⟩ = true ∧
    (cycleGraph 5).adj ⟨0, by omega⟩ ⟨2, by omega⟩ = false := by decide
theorem cycle4_fail_example : 2 * 2 + (cycleGraph 4).minDeg > 4 + 1 := by decide
theorem cycle3_fail_example : (cycleGraph 3).minDeg = 2 := by decide

-- Concrete Sidon set sharpness sanity check: A = {0, 1, 4, 6} in N = 7
def sidon7 (x : Fin 7) : Bool := decide (x.val = 0 ∨ x.val = 1 ∨ x.val = 4 ∨ x.val = 6)
theorem sidon7_sym_defect : symDefectFin 7 sidon7 = 4 := by decide
theorem sidon7_mod_sumset : modSumsetCard 7 sidon7 = 7 := by decide

-- ============================================================================
-- 3. Formalized Disproof of the `lds` Transcription at `n = 9`
-- ============================================================================

def IsLDS {n : Nat} (p : PermFin n) (l : Nat) : Prop :=
  (∃ sub, p.StrictDecSubseq sub ∧ sub.length = l) ∧
  (∀ sub, p.StrictDecSubseq sub → sub.length ≤ l)

/-- Mis-transcribed conjecture (substituting `lds` for `n - lis = des`),
    holding through `n <= 8` (`Av_n(231)`) but false at `n = 9`. -/
def Conj_Avoids231_InvDispLDS : Prop :=
  ∀ (n : Nat) (p : PermFin n) (l : Nat),
    4 ≤ n → p.Avoids231 → IsLDS p l → 2 * p.invCnt ≤ p.disp2 + l * (l - 1)

private def cex9Fn : Fin 9 → Fin 9
  | ⟨0, _⟩ => ⟨8, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨0, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨2, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨4, by omega⟩
  | ⟨7, _⟩ => ⟨7, by omega⟩
  | ⟨8, _⟩ => ⟨6, by omega⟩

private def cex9Inv : Fin 9 → Fin 9
  | ⟨0, _⟩ => ⟨2, by omega⟩
  | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨4, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩
  | ⟨4, _⟩ => ⟨6, by omega⟩
  | ⟨5, _⟩ => ⟨5, by omega⟩
  | ⟨6, _⟩ => ⟨8, by omega⟩
  | ⟨7, _⟩ => ⟨7, by omega⟩
  | ⟨8, _⟩ => ⟨0, by omega⟩

private theorem cex9_left (x : Fin 9) : cex9Inv (cex9Fn x) = x := by
  rcases x with ⟨v, hv⟩
  match v with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl
  | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl

private theorem cex9_right (x : Fin 9) : cex9Fn (cex9Inv x) = x := by
  rcases x with ⟨v, hv⟩
  match v with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl
  | 5 => rfl | 6 => rfl | 7 => rfl | 8 => rfl

/-- Counterexample in `Av_9(231)`: `[8, 1, 0, 3, 2, 5, 4, 7, 6]` has
    `inv_cnt = 12`, `disp2 = 16`, `lds = 3`, giving `24 > 16 + 6 = 22`. -/
def cex231_9 : PermFin 9 where
  toFun := cex9Fn
  invFun := cex9Inv
  left_inv := cex9_left
  right_inv := cex9_right

private theorem sublist_len_le {α : Type} : ∀ {xs ys : List α}, xs.Sublist ys → xs.length ≤ ys.length
  | _, _, .slnil => Nat.le_refl 0
  | _, _, .cons _ h => Nat.le_trans (sublist_len_le h) (Nat.le_succ _)
  | _, _, .cons_cons _ h => Nat.succ_le_succ (sublist_len_le h)

private theorem sublist_cons_cases {α : Type} {x : α} {xs sub : List α}
    (h : sub.Sublist (x :: xs)) :
    sub.Sublist xs ∨ ∃ t, sub = x :: t ∧ t.Sublist xs := by
  cases h with
  | cons _ h' => exact Or.inl h'
  | cons_cons _ h' => exact Or.inr ⟨_, rfl, h'⟩

private theorem sublist_append_split {α : Type} :
    ∀ {xs ys sub : List α}, sub.Sublist (xs ++ ys) →
      ∃ s1 s2, sub = s1 ++ s2 ∧ s1.Sublist xs ∧ s2.Sublist ys
  | [], ys, sub, h => ⟨[], sub, rfl, .slnil, h⟩
  | x :: xt, ys, sub, h => by
    simp only [List.cons_append] at h
    rcases sublist_cons_cases h with h' | ⟨t, rfl, h'⟩
    · rcases sublist_append_split h' with ⟨s1, s2, heq, hs1, hs2⟩
      exact ⟨s1, s2, heq, .cons x hs1, hs2⟩
    · rcases sublist_append_split h' with ⟨s1, s2, heq, hs1, hs2⟩
      exact ⟨x :: s1, s2, by rw [heq, List.cons_append], .cons_cons x hs1, hs2⟩

private theorem pairwise_gt_block_or {xs ys sub : List Nat}
    (hsep : ∀ a ∈ xs, ∀ b ∈ ys, a < b)
    (hsub : sub.Sublist (xs ++ ys)) (hpw : sub.Pairwise (· > ·)) :
    sub.Sublist xs ∨ sub.Sublist ys := by
  rcases sublist_append_split hsub with ⟨s1, s2, heq, hs1, hs2⟩
  cases s1 with
  | nil => rw [List.nil_append] at heq; subst heq; exact Or.inr hs2
  | cons u us =>
    cases s2 with
    | nil => rw [List.append_nil] at heq; subst heq; exact Or.inl hs1
    | cons v vs =>
      exfalso
      rw [heq] at hpw
      have hp := (List.pairwise_append.mp hpw).2.2 u (by simp) v (by simp)
      have hu : u ∈ xs := hs1.subset (by simp)
      have hv : v ∈ ys := hs2.subset (by simp)
      have hlt := hsep u hu v hv
      omega

private theorem cex231_9_avoids : cex231_9.Avoids231 := by
  intro i j k hij hjk
  revert i j k hij hjk
  decide

private theorem tail8_lds_le_2 : ∀ {sub : List Nat},
    sub.Sublist [1, 0, 3, 2, 5, 4, 7, 6] → sub.Pairwise (· > ·) → sub.length ≤ 2 := by
  intro sub hsub hpw
  have h1 : sub.Sublist [1, 0] ∨ sub.Sublist [3, 2, 5, 4, 7, 6] :=
    pairwise_gt_block_or (fun a ha b hb => by simp at ha hb; omega) hsub hpw
  rcases h1 with hA | hrest1
  · exact sublist_len_le hA
  · have h2 : sub.Sublist [3, 2] ∨ sub.Sublist [5, 4, 7, 6] :=
      pairwise_gt_block_or (fun a ha b hb => by simp at ha hb; omega) hrest1 hpw
    rcases h2 with hB | hrest2
    · exact sublist_len_le hB
    · have h3 : sub.Sublist [5, 4] ∨ sub.Sublist [7, 6] :=
        pairwise_gt_block_or (fun a ha b hb => by simp at ha hb; omega) hrest2 hpw
      rcases h3 with hC | hD
      · exact sublist_len_le hC
      · exact sublist_len_le hD

private theorem cex231_9_isLDS : IsLDS cex231_9 3 := by
  refine ⟨⟨[8, 1, 0], ⟨?_, ?_⟩, rfl⟩, ?_⟩
  · change [8, 1, 0].Sublist [8, 1, 0, 3, 2, 5, 4, 7, 6]
    exact List.Sublist.cons_cons 8 (List.Sublist.cons_cons 1 (List.Sublist.cons_cons 0 (List.nil_sublist _)))
  · decide
  · intro sub ⟨hsub, hpw⟩
    have hsub' : sub.Sublist (8 :: [1, 0, 3, 2, 5, 4, 7, 6]) := hsub
    rcases sublist_cons_cases hsub' with htail | ⟨t, rfl, ht⟩
    · exact Nat.le_trans (tail8_lds_le_2 htail hpw) (by omega)
    · have htpw := (List.pairwise_cons.mp hpw).2
      have htle := tail8_lds_le_2 ht htpw
      simp only [List.length_cons]
      omega

private theorem cex231_9_inv : cex231_9.invCnt = 12 := by decide
private theorem cex231_9_disp2 : cex231_9.disp2 = 16 := by decide

theorem not_Conj_Avoids231_InvDispLDS : ¬ Conj_Avoids231_InvDispLDS := by
  intro hconj
  have hbad := hconj 9 cex231_9 3 (by omega) cex231_9_avoids cex231_9_isLDS
  rw [cex231_9_inv, cex231_9_disp2] at hbad
  omega

-- ============================================================================
-- 4. Round-3 Open Conjectures & `decide`-Verified Witnesses
-- ============================================================================

/-- Round-3 Open Target 1 (Graphs — Spectral / Cycle Cancellation):
    Every connected non-tree graph on `n >= 4` vertices satisfies
    `tr(A^4) + 2m <= 2 * M_2(G) + 8 * ind_c4(G)`, equivalently
    `4 * (c_4(G) - ind_c4(G)) <= M_2(G) - M_1(G)`.
    Tight on cycles `C_4` (`40 = 40`) and `C_5` (`40 = 40`), fails on trees such as `K_{1,4}`. -/
def Conj_ConnectedCyclic_TrA4_Zagreb2_IndC4 : Prop :=
  ∀ (n : Nat) (G : SimpleGraphFin n),
    4 ≤ n → G.Connected → ¬ G.IsTree →
    G.trA4 + 2 * G.edgeCount ≤ 2 * G.zagreb2 + 8 * G.indC4Cnt

/-- Round-3 Open Target 2 (Graphs — Allan-Laskar Claw Refinement):
    Every connected graph on `n >= 5` vertices satisfies `2 * i(G) <= 2 * gamma(G) + claws(G)`.
    When `claws(G) = 0`, recovers Allan-Laskar (`i = gamma`). Tight on `P_5` and double star `S_{2,2}`. -/
def Conj_Connected_IndepDom_Claws : Prop :=
  ∀ (n : Nat) (G : SimpleGraphFin n) (i g : Nat),
    5 ≤ n → G.Connected → G.IndepDominationNum i → G.DominationNum g →
    2 * i ≤ 2 * g + G.clawCnt

/-- Round-3 Open Target 3 (Additive Integer Sets — Sum-Dilate + Symmetry Defect):
    Every normalized subset `A subset {0..N-1}` (`0, N-1 in A`, `|A| >= 4`, `N >= 6`)
    satisfies `2 * |A| + sym_defect(A) <= |A + 2A|`. Sharp on `{0, 1, 3, 5}` (`8 + 4 = 12`). -/
def Conj_IntSet_DilateSum_SymDefect : Prop :=
  ∀ (N : Nat) (A : Nat → Bool),
    6 ≤ N → A 0 = true → A (N - 1) = true → (∀ x ≥ N, A x = false) →
    4 ≤ cardPrefix A N →
    2 * cardPrefix A N + symDefectInterval A 0 (N - 1) ≤ intDilateSum2Card A N

/-- Round-3 Open Target 4 (Permutations — Two-Pass West Stack Sorting on `Av(321)`):
    Every `321`-avoiding permutation `p` of length `n >= 4` satisfies
    `3 * inv(S^2(p)) <= pat_231(p)`. Sharp on `[1, 2, 3, 0]`; fails outside `Av(321)` on `[2, 1, 3, 0]`. -/
def Conj_Av321_TwoStackInv_Pat231 : Prop :=
  ∀ (n : Nat) (p : PermFin n),
    4 ≤ n → p.Avoids321 → 3 * p.stack2Inv ≤ p.pat231

def starGraph (n : Nat) : SimpleGraphFin n where
  adj u v := decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (v.val = 0 ∧ u.val ≠ 0))
  symm u v := by
    by_cases hu : u.val = 0 <;> by_cases hv : v.val = 0 <;> simp [hu, hv]
  loopless u := by
    by_cases hu : u.val = 0 <;> simp [hu]

theorem cycle4_trA4_sharp :
    (cycleGraph 4).trA4 + 2 * (cycleGraph 4).edgeCount =
    2 * (cycleGraph 4).zagreb2 + 8 * (cycleGraph 4).indC4Cnt := by decide

theorem cycle5_trA4_sharp :
    (cycleGraph 5).trA4 + 2 * (cycleGraph 5).edgeCount =
    2 * (cycleGraph 5).zagreb2 + 8 * (cycleGraph 5).indC4Cnt := by decide

theorem star5_edgeCount : (starGraph 5).edgeCount = 4 := by decide

theorem star5_tree_fails_trA4 :
    (starGraph 5).trA4 + 2 * (starGraph 5).edgeCount >
    2 * (starGraph 5).zagreb2 + 8 * (starGraph 5).indC4Cnt := by decide

private def isDoubleStarEdge (u v : Nat) : Bool :=
  (u == 0 && (v == 1 || v == 2 || v == 3)) ||
  (v == 0 && (u == 1 || u == 2 || u == 3)) ||
  (u == 1 && (v == 4 || v == 5)) ||
  (v == 1 && (u == 4 || u == 5))

def doubleStar6 : SimpleGraphFin 6 where
  adj u v := isDoubleStarEdge u.val v.val
  symm u v := by revert u v; decide
  loopless u := by revert u; decide

theorem doubleStar6_clawCnt : doubleStar6.clawCnt = 2 := by decide

theorem doubleStar6_dom_indepDom_sharp :
    let D : List (Fin 6) := [⟨0, by omega⟩, ⟨1, by omega⟩]
    let I : List (Fin 6) := [⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩]
    D.Nodup ∧ (∀ v : Fin 6, v ∈ D ∨ ∃ u ∈ D, doubleStar6.adj u v = true) ∧
    I.Nodup ∧ (∀ u ∈ I, ∀ v ∈ I, doubleStar6.adj u v = false) ∧
    (∀ v : Fin 6, v ∈ I ∨ ∃ u ∈ I, doubleStar6.adj u v = true) ∧
    2 * I.length = 2 * D.length + doubleStar6.clawCnt := by decide

def asymSet6 (x : Nat) : Bool := decide (x = 0 ∨ x = 1 ∨ x = 3 ∨ x = 5)

theorem asymSet6_sharp :
    cardPrefix asymSet6 6 = 4 ∧
    symDefectInterval asymSet6 0 5 = 4 ∧
    intDilateSum2Card asymSet6 6 = 12 ∧
    2 * cardPrefix asymSet6 6 + symDefectInterval asymSet6 0 5 =
      intDilateSum2Card asymSet6 6 := by decide

private def p1230Fn : Fin 4 → Fin 4
  | ⟨0, _⟩ => ⟨1, by omega⟩ | ⟨1, _⟩ => ⟨2, by omega⟩
  | ⟨2, _⟩ => ⟨3, by omega⟩ | ⟨3, _⟩ => ⟨0, by omega⟩

private def p1230Inv : Fin 4 → Fin 4
  | ⟨0, _⟩ => ⟨3, by omega⟩ | ⟨1, _⟩ => ⟨0, by omega⟩
  | ⟨2, _⟩ => ⟨1, by omega⟩ | ⟨3, _⟩ => ⟨2, by omega⟩

def perm1230 : PermFin 4 where
  toFun := p1230Fn
  invFun := p1230Inv
  left_inv x := by rcases x with ⟨v, hv⟩; match v with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
  right_inv x := by rcases x with ⟨v, hv⟩; match v with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl

theorem perm1230_avoids321 : perm1230.Avoids321 := by
  intro i j k hij hjk
  revert i j k hij hjk
  decide

theorem perm1230_sharp :
    perm1230.stack2Inv = 1 ∧ perm1230.pat231 = 3 ∧
    3 * perm1230.stack2Inv = perm1230.pat231 := by decide

private def p2130Fn : Fin 4 → Fin 4
  | ⟨0, _⟩ => ⟨2, by omega⟩ | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨3, by omega⟩ | ⟨3, _⟩ => ⟨0, by omega⟩

private def p2130Inv : Fin 4 → Fin 4
  | ⟨0, _⟩ => ⟨3, by omega⟩ | ⟨1, _⟩ => ⟨1, by omega⟩
  | ⟨2, _⟩ => ⟨0, by omega⟩ | ⟨3, _⟩ => ⟨2, by omega⟩

def perm2130 : PermFin 4 where
  toFun := p2130Fn
  invFun := p2130Inv
  left_inv x := by rcases x with ⟨v, hv⟩; match v with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
  right_inv x := by rcases x with ⟨v, hv⟩; match v with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl

theorem perm2130_fails_without_321 :
    ¬ perm2130.Avoids321 ∧ 3 * perm2130.stack2Inv > perm2130.pat231 := by
  refine ⟨?_, by decide⟩
  intro h
  have bad : ¬ ((perm2130.toFun ⟨0, by omega⟩).val > (perm2130.toFun ⟨1, by omega⟩).val ∧
      (perm2130.toFun ⟨1, by omega⟩).val > (perm2130.toFun ⟨3, by omega⟩).val) :=
    h ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨3, by omega⟩ (by decide) (by decide)
  exact bad (by decide)

-- ============================================================================
-- 5. Round-4 Open Conjectures & `decide`-Verified Witnesses
-- ============================================================================

/-- Round-4 Open Target 1 (Graphs — Bipartite Domination vs Induced Matching + Diameter):
    Every connected bipartite graph `G` on `n >= 5` vertices satisfies
    `gamma(G) + 1 <= ind_nu(G) + diam(G)`.
    Sharp on `K_{2,3}` (`2 + 1 = 1 + 2`); fails without bipartiteness on an 8-vertex
    `(2,2,1,1,2)` blowup of `C_5` (`gamma = 3, ind_nu = 1, diam = 2`, `3 + 1 > 1 + 2`). -/
def Conj_Bipartite_Dom_IndNu_Diam : Prop :=
  ∀ (n : Nat) (G : SimpleGraphFin n) (g iu d : Nat),
    5 ≤ n → G.Connected → G.Bipartite →
    G.DominationNum g → G.InducedMatchingNum iu → G.DiameterNum d →
    g + 1 ≤ iu + d

/-- Round-4 Open Target 2 (Additive Integer Sets — `|A + 3A|` + Symmetry Defect):
    Every normalized subset `A subset {0..N-1}` (`0, N-1 in A`, `|A| >= 5`, `N >= 8`)
    satisfies `3 * |A| + sym_defect(A) <= |A + 3A| + 2`.
    Sharp on the infinite family `{0, 3, ..., 3(k-2), 3k-5}`, starting at `N = 11`, `k = 5`. -/
def Conj_IntSet_Dilate3Sum_SymDefect : Prop :=
  ∀ (N : Nat) (A : Nat → Bool),
    8 ≤ N → A 0 = true → A (N - 1) = true → (∀ x ≥ N, A x = false) →
    5 ≤ cardPrefix A N →
    3 * cardPrefix A N + symDefectInterval A 0 (N - 1) ≤ intDilateSum3Card A N + 2

/-- Round-4 Open Target 3 (Permutations — One-Pass West Stack vs Pop-Stack Dominance):
    Every permutation `p` of length `n >= 4` satisfies `inv(S(p)) <= inv(P(p))`,
    where `S` is West's stack-sorting map and `P` reverses each maximal descending run. -/
def Conj_AllPerms_StackInv_Le_PopInv : Prop :=
  ∀ (n : Nat) (p : PermFin n),
    4 ≤ n → p.stackInv ≤ p.popInv

def k23Graph : SimpleGraphFin 5 where
  adj u v := decide ((u.val < 2 ∧ 2 ≤ v.val) ∨ (2 ≤ u.val ∧ v.val < 2))
  symm u v := by revert u v; decide
  loopless u := by revert u; decide

theorem k23Graph_bipartite : k23Graph.Bipartite := by
  refine ⟨fun u => decide (u.val < 2), ?_⟩
  decide

theorem k23Graph_bipartite_sharp :
    let col : Fin 5 → Bool := fun u => decide (u.val < 2)
    let D : List (Fin 5) := [⟨0, by omega⟩, ⟨2, by omega⟩]
    (∀ u v : Fin 5, k23Graph.adj u v = true → col u != col v) ∧
    D.Nodup ∧ (∀ v : Fin 5, v ∈ D ∨ ∃ u ∈ D, k23Graph.adj u v = true) ∧
    (∀ a : Fin 5, (List.finRange 5).any (fun v => decide (v ≠ a) && !(k23Graph.adj a v)) = true) ∧
    k23Graph.adj ⟨0, by omega⟩ ⟨2, by omega⟩ = true ∧
    (∀ u1 v1 u2 v2 : Fin 5,
      k23Graph.adj u1 v1 = true → k23Graph.adj u2 v2 = true →
      u1 ≠ u2 → u1 ≠ v2 → v1 ≠ u2 → v1 ≠ v2 →
      k23Graph.adj u1 u2 = true ∨ k23Graph.adj u1 v2 = true ∨
      k23Graph.adj v1 u2 = true ∨ k23Graph.adj v1 v2 = true) ∧
    (∀ u v : Fin 5, u = v ∨ k23Graph.adj u v = true ∨
      (List.finRange 5).any (fun w => k23Graph.adj u w && k23Graph.adj w v) = true) ∧
    k23Graph.adj ⟨0, by omega⟩ ⟨1, by omega⟩ = false ∧
    D.length + 1 = 1 + 2 := by
  dsimp only
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

private def nonBip8Adj (u v : Nat) : Bool :=
  (u == 0 && (v == 2 || v == 3 || v == 5 || v == 6)) ||
  (u == 1 && (v == 4 || v == 5 || v == 6)) ||
  (u == 2 && (v == 0 || v == 4 || v == 7)) ||
  (u == 3 && (v == 0 || v == 4 || v == 7)) ||
  (u == 4 && (v == 1 || v == 2 || v == 3)) ||
  (u == 5 && (v == 0 || v == 1 || v == 7)) ||
  (u == 6 && (v == 0 || v == 1 || v == 7)) ||
  (u == 7 && (v == 2 || v == 3 || v == 5 || v == 6))

/-- Balanced `(2,2,1,1,2)` blowup of `C_5` on 8 vertices: `gamma = 3`, `ind_nu = 1`, `diam = 2`. -/
def nonBip8 : SimpleGraphFin 8 where
  adj u v := nonBip8Adj u.val v.val
  symm u v := by revert u v; decide
  loopless u := by revert u; decide

theorem nonBip8_fails_without_bipartite :
    ¬ nonBip8.Bipartite ∧
    (∀ u v : Fin 8, u = v ∨ nonBip8.adj u v = true ∨
      (List.finRange 8).any (fun w => nonBip8.adj u w && nonBip8.adj w v) = true) ∧
    (∀ a b : Fin 8, (List.finRange 8).any (fun v =>
      decide (v ≠ a) && decide (v ≠ b) && !(nonBip8.adj a v) && !(nonBip8.adj b v)) = true) ∧
    (∀ u1 v1 u2 v2 : Fin 8,
      u1.val < v1.val → u2.val < v2.val → u1.val < u2.val →
      nonBip8.adj u1 v1 = true → nonBip8.adj u2 v2 = true →
      v1 ≠ u2 → v1 ≠ v2 →
      nonBip8.adj u1 u2 = true ∨ nonBip8.adj u1 v2 = true ∨
      nonBip8.adj v1 u2 = true ∨ nonBip8.adj v1 v2 = true) ∧
    3 + 1 > 1 + 2 := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  intro ⟨col, hcol⟩
  have h02 := hcol ⟨0, by omega⟩ ⟨2, by omega⟩ (by decide)
  have h24 := hcol ⟨2, by omega⟩ ⟨4, by omega⟩ (by decide)
  have h41 := hcol ⟨4, by omega⟩ ⟨1, by omega⟩ (by decide)
  have h15 := hcol ⟨1, by omega⟩ ⟨5, by omega⟩ (by decide)
  have h50 := hcol ⟨5, by omega⟩ ⟨0, by omega⟩ (by decide)
  revert h02 h24 h41 h15 h50
  cases col ⟨0, by omega⟩ <;> cases col ⟨2, by omega⟩ <;> cases col ⟨4, by omega⟩ <;>
    cases col ⟨1, by omega⟩ <;> cases col ⟨5, by omega⟩ <;> decide

def asymSet11 (x : Nat) : Bool := decide (x = 0 ∨ x = 3 ∨ x = 6 ∨ x = 9 ∨ x = 10)

theorem asymSet11_dilate3_sharp :
    cardPrefix asymSet11 11 = 5 ∧
    symDefectInterval asymSet11 0 10 = 6 ∧
    intDilateSum3Card asymSet11 11 = 19 ∧
    3 * cardPrefix asymSet11 11 + symDefectInterval asymSet11 0 10 =
      intDilateSum3Card asymSet11 11 + 2 := by decide

def asymSet5_k3 (x : Nat) : Bool := decide (x = 0 ∨ x = 3 ∨ x = 4)

theorem asymSet5_k3_fails_below_k5 :
    cardPrefix asymSet5_k3 5 = 3 ∧
    symDefectInterval asymSet5_k3 0 4 = 2 ∧
    intDilateSum3Card asymSet5_k3 5 = 8 ∧
    3 * cardPrefix asymSet5_k3 5 + symDefectInterval asymSet5_k3 0 4 >
      intDilateSum3Card asymSet5_k3 5 + 2 := by decide

theorem perm2130_stack_eq_pop_nonzero :
    perm2130.stackInv = 2 ∧ perm2130.popInv = 2 ∧
    perm2130.stackInv = perm2130.popInv := by decide

-- ============================================================================
-- 6. Round-5 Open Conjectures (`n <= 64 / N <= 256` SA-Hardened & Farkas-Irreducible)
-- ============================================================================

/-- Round-5 Open Target 1 (Permutations — West Stack Descents vs Input Peaks):
    Every permutation `p` of length `n >= 4` satisfies `des(S(p)) <= peaks(p)`.
    Survived `36M` permutations (`n <= 64`) and `393,216` SA steps with `204,985`
    equality hits (`eq_sizes = 60`), plus exhaustive `n <= 8` checks; sharp on `perm1230`. -/
def Conj_AllPerms_StackDes_Le_Peaks : Prop :=
  ∀ (n : Nat) (p : PermFin n),
    4 ≤ n → p.stackDes ≤ p.peaksCnt

/-- Round-5 Open Target 2 (Additive Integer Sets — Restricted Sumset + Symmetry Defect):
    Every normalized subset `A subset {0..N-1}` (`0, N-1 in A`, `|A| >= 4`, `N >= 6`)
    satisfies `|A| + sym_defect(A) <= |A ^+ A| + 2`.
    Survived `30.78M` normalized `k >= 4` sets (`N <= 256`), `393,216` SA steps (`439` equality
    hits, `57` large `N >= 40` tight sizes), and exhaustive `N <= 16`; sharp on `asymSet6`. -/
def Conj_IntSet_RestSum_SymDefect : Prop :=
  ∀ (N : Nat) (A : Nat → Bool),
    6 ≤ N → A 0 = true → A (N - 1) = true → (∀ x ≥ N, A x = false) →
    4 ≤ cardPrefix A N →
    cardPrefix A N + symDefectInterval A 0 (N - 1) ≤ intRestSumCard A N + 2

theorem perm1230_stackDes_eq_peaks :
    perm1230.stackDes = 1 ∧ perm1230.peaksCnt = 1 ∧
    perm1230.stackDes = perm1230.peaksCnt := by decide

theorem cex231_9_stackDes_lt_peaks :
    cex231_9.stackDes = 0 ∧ cex231_9.peaksCnt = 3 ∧
    cex231_9.stackDes < cex231_9.peaksCnt := by decide

theorem asymSet6_restSum_sharp :
    cardPrefix asymSet6 6 = 4 ∧
    symDefectInterval asymSet6 0 5 = 4 ∧
    intRestSumCard asymSet6 6 = 6 ∧
    cardPrefix asymSet6 6 + symDefectInterval asymSet6 0 5 =
      intRestSumCard asymSet6 6 + 2 := by decide

def unnormSet6 (x : Nat) : Bool := decide (x < 4)

theorem unnormSet6_fails_without_norm :
    unnormSet6 5 = false ∧
    cardPrefix unnormSet6 6 = 4 ∧
    symDefectInterval unnormSet6 0 5 = 4 ∧
    intRestSumCard unnormSet6 6 = 5 ∧
    cardPrefix unnormSet6 6 + symDefectInterval unnormSet6 0 5 >
      intRestSumCard unnormSet6 6 + 2 := by decide

-- ============================================================================
-- 7. Round-9 Formal Disproof of `Conj_Bipartite_Dom_IndNu_Diam` at `n = 25`
-- ============================================================================
-- Discovered via Round-9 `u64`-offset Tree-64 GPU mining (`151` failing trees starting at
-- offset `110,024,707`), distilled to the minimal 25-vertex tree `tree25` (`1` root + `6`
-- 4-vertex arms `0 - u_k`, `u_k - x_k`, `u_k - v_k - y_k`), where `gamma = 12`,
-- `ind_nu = 6`, `diam = 6`, so `gamma + 1 = 13 > 12 = ind_nu + diam`.

private def tree25Parent (v : Nat) : Nat :=
  if v % 4 == 1 then 0 else if v % 4 == 3 then v - 2 else v - 1

def tree25 : SimpleGraphFin 25 where
  adj u v :=
    (decide (1 ≤ u.val) && decide (tree25Parent u.val = v.val)) ||
    (decide (1 ≤ v.val) && decide (tree25Parent v.val = u.val))
  symm u v := by revert u v; decide
  loopless u := by revert u; decide

private theorem tree25_bipartite : tree25.Bipartite := by
  refine ⟨fun u => decide (u.val % 4 == 1 || (u.val % 4 == 0 && u.val != 0)), ?_⟩
  decide

private def isWalkBool {n : Nat} (G : SimpleGraphFin n) : List (Fin n) → Bool
  | [] => true
  | [_] => true
  | a :: b :: r => G.adj a b && isWalkBool G (b :: r)

private theorem isWalkBool_imp {n : Nat} (G : SimpleGraphFin n) :
    ∀ w : List (Fin n), isWalkBool G w = true → G.IsWalk w
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: r, h => by
    simp only [isWalkBool, Bool.and_eq_true] at h
    exact ⟨h.1, isWalkBool_imp G (b :: r) h.2⟩

private def pathToRoot25 (u : Fin 25) : List (Fin 25) :=
  if h0 : u.val = 0 then [u]
  else if h1 : u.val % 4 = 1 then [u, ⟨0, by omega⟩]
  else if h2 : u.val % 4 = 2 then [u, ⟨u.val - 1, by omega⟩, ⟨0, by omega⟩]
  else if h3 : u.val % 4 = 3 then [u, ⟨u.val - 2, by omega⟩, ⟨0, by omega⟩]
  else [u, ⟨u.val - 1, by omega⟩, ⟨u.val - 3, by omega⟩, ⟨0, by omega⟩]

private def walk25 (s t : Fin 25) : List (Fin 25) :=
  (pathToRoot25 s).dropLast ++ (pathToRoot25 t).reverse

private def checkWalk25 (s t : Fin 25) : Bool :=
  decide (walk25 s t ≠ []) &&
  decide ((walk25 s t).head? = some s) &&
  decide ((walk25 s t).getLast? = some t) &&
  isWalkBool tree25 (walk25 s t) &&
  decide ((walk25 s t).length ≤ 7)

private theorem checkWalk25_all : ∀ s t : Fin 25, checkWalk25 s t = true := by decide

private theorem tree25_within6 (s t : Fin 25) : tree25.WithinDist s t 6 := by
  have h := checkWalk25_all s t
  simp only [checkWalk25, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨walk25 s t, h.1.1.1.1, h.1.1.1.2, h.1.1.2, isWalkBool_imp tree25 _ h.1.2, h.2⟩

private theorem tree25_connected : tree25.Connected := by
  intro s t
  rcases tree25_within6 s t with ⟨w, h1, h2, h3, h4, _⟩
  exact ⟨w, h1, h2, h3, h4⟩

private def dist4_25 (u : Fin 25) : Nat :=
  if u.val == 4 then 0
  else if u.val == 3 then 1
  else if u.val == 1 || u.val == 2 then 2
  else if u.val == 0 then 3
  else if u.val % 4 == 1 then 4
  else if u.val % 4 == 2 || u.val % 4 == 3 then 5
  else 6

private theorem dist4_step :
    ∀ a b : Fin 25, tree25.adj a b = true → dist4_25 b ≤ dist4_25 a + 1 := by decide

private theorem dist4_walk :
    ∀ (w : List (Fin 25)) (s t : Fin 25),
      w ≠ [] → w.head? = some s → w.getLast? = some t → tree25.IsWalk w →
      dist4_25 t ≤ dist4_25 s + (w.length - 1)
  | [], _, _, hne, _, _, _ => absurd rfl hne
  | [a], s, t, _, hh, hl, _ => by
    simp at hh hl
    subst hh; subst hl; simp
  | a :: b :: r, s, t, _, hh, hl, hw => by
    simp at hh
    subst hh
    have hst := dist4_step a b hw.1
    have ih := dist4_walk (b :: r) b t (by simp) rfl (by simpa using hl) hw.2
    simp only [List.length_cons] at ih ⊢
    omega

private theorem tree25_diam6 : tree25.DiameterNum 6 := by
  refine ⟨tree25_within6, ?_⟩
  intro d' hd'
  rcases hd' ⟨4, by decide⟩ ⟨8, by decide⟩ with ⟨w, hne, hh, hl, hw, hlen⟩
  have hbw := dist4_walk w ⟨4, by decide⟩ ⟨8, by decide⟩ hne hh hl hw
  have hd4 : dist4_25 ⟨4, by decide⟩ = 0 := rfl
  have hd8 : dist4_25 ⟨8, by decide⟩ = 6 := rfl
  omega

private def domSet25 : List (Fin 25) :=
  [⟨1, by omega⟩, ⟨3, by omega⟩, ⟨5, by omega⟩, ⟨7, by omega⟩,
   ⟨9, by omega⟩, ⟨11, by omega⟩, ⟨13, by omega⟩, ⟨15, by omega⟩,
   ⟨17, by omega⟩, ⟨19, by omega⟩, ⟨21, by omega⟩, ⟨23, by omega⟩]

private theorem domSet25_check :
    domSet25.Nodup ∧
    ∀ v : Fin 25, (decide (v ∈ domSet25) || domSet25.any (fun u => tree25.adj u v)) = true := by
  decide

private def leaves25 (j : Fin 12) : Fin 25 := ⟨2 * j.val + 2, by omega⟩

private def leafSlot25 (z : Fin 25) : Nat :=
  if z.val = 0 then 12 else (z.val - 1) / 2

private theorem leafSlot25_hit :
    ∀ (j : Fin 12) (z : Fin 25),
      (z = leaves25 j ∨ tree25.adj z (leaves25 j) = true) → leafSlot25 z = j.val := by
  decide

private theorem leafSlot25_col_le1 :
    ∀ z : Fin 25,
      sumNat (List.finRange 12) (fun j => if decide (leafSlot25 z = j.val) then 1 else 0) ≤ 1 := by
  decide

private theorem one_le_sumNat_mem {α : Type} (xs : List α) (f : α → Nat)
    {a : α} (ha : a ∈ xs) (hf : 1 ≤ f a) : 1 ≤ sumNat xs f := by
  induction xs with
  | nil => simp at ha
  | cons x rest ih =>
    simp only [sumNat]
    rcases List.mem_cons.mp ha with rfl | hr
    · omega
    · have := ih hr; omega

private theorem sumNat_const_one {α : Type} (xs : List α) :
    sumNat xs (fun _ => 1) = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ rest ih => simp only [sumNat, List.length_cons, ih]; omega

private theorem tree25_dom12 : tree25.DominationNum 12 := by
  refine ⟨⟨domSet25, ⟨domSet25_check.1, ?_⟩, rfl⟩, ?_⟩
  · intro v
    have hv := domSet25_check.2 v
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hv
    exact hv
  · intro D hD
    have h12 : sumNat (List.finRange 12) (fun _ => 1) = 12 := by
      rw [sumNat_const_one, List.length_finRange]
    have hlow : 12 ≤ sumNat (List.finRange 12) (fun j =>
        sumNat D (fun z => if decide (leafSlot25 z = j.val) then 1 else 0)) := by
      rw [← h12]
      apply sumNat_mono
      intro j _
      rcases hD.2 (leaves25 j) with hmem | ⟨u, hu, hadj⟩
      · refine one_le_sumNat_mem D _ hmem ?_
        have hs := leafSlot25_hit j (leaves25 j) (Or.inl rfl)
        simp [hs]
      · refine one_le_sumNat_mem D _ hu ?_
        have hs := leafSlot25_hit j u (Or.inr hadj)
        simp [hs]
    have hsw := sumNat_swap (List.finRange 12) D (fun j z => if decide (leafSlot25 z = j.val) then 1 else 0)
    have hup : sumNat D (fun z => sumNat (List.finRange 12) (fun j => if decide (leafSlot25 z = j.val) then 1 else 0)) ≤
        sumNat D (fun _ => 1) := by
      apply sumNat_mono
      intro z _
      exact leafSlot25_col_le1 z
    have hlen := sumNat_const_one D
    omega

private def indMatch25 : List (Fin 25 × Fin 25) :=
  [(⟨1, by omega⟩, ⟨2, by omega⟩), (⟨5, by omega⟩, ⟨6, by omega⟩),
   (⟨9, by omega⟩, ⟨10, by omega⟩), (⟨13, by omega⟩, ⟨14, by omega⟩),
   (⟨17, by omega⟩, ⟨18, by omega⟩), (⟨21, by omega⟩, ⟨22, by omega⟩)]

private theorem indMatch25_ok :
    (∀ e ∈ indMatch25, e.1.val < e.2.val ∧ tree25.adj e.1 e.2 = true) ∧
    (indMatch25.flatMap (fun e => [e.1, e.2])).Nodup ∧
    (∀ e1 ∈ indMatch25, ∀ e2 ∈ indMatch25, e1 ≠ e2 →
      tree25.adj e1.1 e2.1 = false ∧ tree25.adj e1.1 e2.2 = false ∧
      tree25.adj e1.2 e2.1 = false ∧ tree25.adj e1.2 e2.2 = false) := by
  decide

private def armEdges25 (k : Fin 6) : List (Fin 25 × Fin 25) :=
  [(⟨0, by omega⟩, ⟨4 * k.val + 1, by omega⟩),
   (⟨4 * k.val + 1, by omega⟩, ⟨4 * k.val + 2, by omega⟩),
   (⟨4 * k.val + 1, by omega⟩, ⟨4 * k.val + 3, by omega⟩),
   (⟨4 * k.val + 3, by omega⟩, ⟨4 * k.val + 4, by omega⟩)]

private theorem arm25_lt6 :
    ∀ a b : Fin 25, a.val < b.val → tree25.adj a b = true → (b.val - 1) / 4 < 6 := by
  decide

private theorem armEdges25_mem :
    ∀ (k : Fin 6) (a b : Fin 25),
      a.val < b.val → tree25.adj a b = true → (b.val - 1) / 4 = k.val →
      (a, b) ∈ armEdges25 k := by
  decide

private def armPairOk25 (e1 e2 : Fin 25 × Fin 25) : Bool :=
  !(decide (e1.1 ≠ e2.1) && decide (e1.1 ≠ e2.2) &&
    decide (e1.2 ≠ e2.1) && decide (e1.2 ≠ e2.2) &&
    !(tree25.adj e1.1 e2.1) && !(tree25.adj e1.1 e2.2) &&
    !(tree25.adj e1.2 e2.1) && !(tree25.adj e1.2 e2.2))

private theorem armEdges25_conflict_bool :
    ∀ k : Fin 6,
      ((armEdges25 k).all (fun e1 => (armEdges25 k).all (fun e2 => armPairOk25 e1 e2))) = true := by
  decide

private theorem armEdges25_conflict (k : Fin 6) {e1 e2 : Fin 25 × Fin 25}
    (hm1 : e1 ∈ armEdges25 k) (hm2 : e2 ∈ armEdges25 k)
    (d1 : e1.1 ≠ e2.1) (d2 : e1.1 ≠ e2.2) (d3 : e1.2 ≠ e2.1) (d4 : e1.2 ≠ e2.2)
    (a1 : tree25.adj e1.1 e2.1 = false) (a2 : tree25.adj e1.1 e2.2 = false)
    (a3 : tree25.adj e1.2 e2.1 = false) (a4 : tree25.adj e1.2 e2.2 = false) : False := by
  have hb1 := (List.all_eq_true.mp (armEdges25_conflict_bool k)) e1 hm1
  have hb2 := (List.all_eq_true.mp hb1) e2 hm2
  simp [armPairOk25, d1, d2, d3, d4, a1, a2, a3, a4] at hb2

private theorem matching_edges_disj {n : Nat} {M : List (Fin n × Fin n)}
    (hnd : (M.flatMap (fun e => [e.1, e.2])).Nodup) :
    M.Pairwise (fun e1 e2 =>
      e1.1 ≠ e2.1 ∧ e1.1 ≠ e2.2 ∧ e1.2 ≠ e2.1 ∧ e1.2 ≠ e2.2) := by
  induction M with
  | nil => exact .nil
  | cons e rest ih =>
    simp only [List.flatMap_cons, List.nodup_append] at hnd
    rcases hnd with ⟨_, hrest_nd, hdisj⟩
    refine .cons ?_ (ih hrest_nd)
    intro e2 he2
    have hm1 : e2.1 ∈ rest.flatMap (fun x => [x.1, x.2]) :=
      List.mem_flatMap.mpr ⟨e2, he2, by simp⟩
    have hm2 : e2.2 ∈ rest.flatMap (fun x => [x.1, x.2]) :=
      List.mem_flatMap.mpr ⟨e2, he2, by simp⟩
    exact ⟨hdisj e.1 (by simp) e2.1 hm1, hdisj e.1 (by simp) e2.2 hm2,
           hdisj e.2 (by simp) e2.1 hm1, hdisj e.2 (by simp) e2.2 hm2⟩

private theorem sumNat_bool_eq_zero {α : Type} (ys : List α) (P : α → Bool)
    (hall : ∀ y ∈ ys, P y = false) :
    sumNat ys (fun y => if P y then 1 else 0) = 0 := by
  induction ys with
  | nil => rfl
  | cons y yr ih =>
    have hy : P y = false := hall y (by simp)
    have hr := ih (fun z hz => hall z (by simp [hz]))
    simp [sumNat, hy, hr]

private theorem sumNat_bool_le_one_of_pairwise {α : Type} (xs : List α) (P : α → Bool)
    (R : α → α → Prop) (hpw : xs.Pairwise R)
    (hconf : ∀ a ∈ xs, ∀ b ∈ xs, R a b → P a = true → P b = true → False) :
    sumNat xs (fun x => if P x then 1 else 0) ≤ 1 := by
  induction xs with
  | nil => simp [sumNat]
  | cons x rest ih =>
    cases hpw with
    | cons hx hrest =>
      simp only [sumNat]
      cases hpx : P x with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        exact ih hrest (fun a ha b hb hr => hconf a (by simp [ha]) b (by simp [hb]) hr)
      | true =>
        have hz : sumNat rest (fun y => if P y then 1 else 0) = 0 := by
          apply sumNat_bool_eq_zero
          intro y hy
          cases hpy : P y with
          | false => rfl
          | true => exact False.elim (hconf x (by simp) y (by simp [hy]) (hx y hy) hpx hpy)
        rw [hz]; simp

private theorem tree25_indNu6 : tree25.InducedMatchingNum 6 := by
  refine ⟨⟨indMatch25, ⟨⟨indMatch25_ok.1, indMatch25_ok.2.1⟩, indMatch25_ok.2.2⟩, rfl⟩, ?_⟩
  intro M hM
  have hpw := matching_edges_disj hM.1.2
  have hlen : M.length = sumNat M (fun _ => 1) := (sumNat_const_one M).symm
  have hcov : sumNat M (fun _ => 1) ≤
      sumNat M (fun e => sumNat (List.finRange 6) (fun k => if decide ((e.2.val - 1) / 4 = k.val) then 1 else 0)) := by
    apply sumNat_mono
    intro e he
    have he_ok := hM.1.1 e he
    have hk_lt := arm25_lt6 e.1 e.2 he_ok.1 he_ok.2
    refine one_le_sumNat_mem (List.finRange 6) _ (List.mem_finRange ⟨(e.2.val - 1) / 4, hk_lt⟩) ?_
    simp
  have hsw := sumNat_swap M (List.finRange 6) (fun e k => if decide ((e.2.val - 1) / 4 = k.val) then 1 else 0)
  have hcol : sumNat (List.finRange 6) (fun k =>
      sumNat M (fun e => if decide ((e.2.val - 1) / 4 = k.val) then 1 else 0)) ≤
      sumNat (List.finRange 6) (fun _ => 1) := by
    apply sumNat_mono
    intro k _
    refine sumNat_bool_le_one_of_pairwise M _ _ hpw ?_
    intro e1 he1 e2 he2 hdisj hp1 hp2
    have hne : e1 ≠ e2 := fun heq => hdisj.1 (heq ▸ rfl)
    have he1_ok := hM.1.1 e1 he1
    have he2_ok := hM.1.1 e2 he2
    have hk1 : (e1.2.val - 1) / 4 = k.val := of_decide_eq_true hp1
    have hk2 : (e2.2.val - 1) / 4 = k.val := of_decide_eq_true hp2
    have hm1 := armEdges25_mem k e1.1 e1.2 he1_ok.1 he1_ok.2 hk1
    have hm2 := armEdges25_mem k e2.1 e2.2 he2_ok.1 he2_ok.2 hk2
    have hind := hM.2 e1 he1 e2 he2 hne
    exact armEdges25_conflict k hm1 hm2
      hdisj.1 hdisj.2.1 hdisj.2.2.1 hdisj.2.2.2
      hind.1 hind.2.1 hind.2.2.1 hind.2.2.2
  have h6 : sumNat (List.finRange 6) (fun _ => 1) = 6 := by
    rw [sumNat_const_one, List.length_finRange]
  omega

/-- **Round-9 Formal Disproof of `Conj_Bipartite_Dom_IndNu_Diam`:**
    The 25-vertex tree `tree25` is connected and bipartite with `gamma = 12`,
    `ind_nu = 6`, and `diam = 6`, violating `gamma + 1 <= ind_nu + diam` (`13 > 12`). -/
theorem not_Conj_Bipartite_Dom_IndNu_Diam : ¬ Conj_Bipartite_Dom_IndNu_Diam := by
  intro h
  have hbad := h 25 tree25 12 6 6 (by omega) tree25_connected tree25_bipartite
    tree25_dom12 tree25_indNu6 tree25_diam6
  omega

end CombMining
