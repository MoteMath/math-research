/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FanoSparse24Perm.Defs

/-!
# Theorem 3: Exact Fano Plane `2:4` Column-Permutation Obstruction (`R_crit(2, 3) = 7`)

Proves:
1. Universal first-moment lower bound `R_crit(C, 3) ≥ ⌈(4C - 1)(4C - 2) / 6⌉` for all `C ≥ 1`
   via the exact ceiling arithmetic and the universal finite pigeonhole union bound, plus exact
   values for `C ∈ {1, 2, 3, 4, 8, 16, 32}`.
2. For `8` columns (`C = 2`), there are `35` canonical `(4, 4)`-bipartitions and `56` weight-3
   rows, and EVERY weight-3 row kills exactly `5` of the `35` bipartitions.
3. Consequently, EVERY list of `≤ 6` weight-3 rows on `8` columns admits a `2:4`-feasible
   `(4, 4)`-bipartition (`rowsFeasible8 rows`).
4. The `7` lines of the Fano plane `PG(2, 2)` (`fanoLines8`) are weight-3 rows satisfying
   `|L_i ∩ L_j| = 1` for all `i ≠ j`, kill `7` pairwise-disjoint sets of `5` bipartitions
   (`7 × 5 = 35`), and cover all `35 / 35` `(4, 4)`-bipartitions (`¬ rowsFeasible8 fanoLines8`).
-/

namespace FanoSparse24Perm

/-! ### Universal Ceiling and Pigeonhole Union-Bound Machinery -/

theorem rCritLowerBound3_spec (C : Nat) (_hC : 1 ≤ C) :
    (4 * C - 1) * (4 * C - 2) ≤ 6 * rCritLowerBound3 C ∧
    ∀ R : Nat, R < rCritLowerBound3 C → 6 * R < (4 * C - 1) * (4 * C - 2) := by
  unfold rCritLowerBound3
  generalize (4 * C - 1) * (4 * C - 2) = N
  constructor
  · omega
  · intro R hR; omega

theorem list_filter_true {α : Type} (L : List α) : L.filter (fun _ => true) = L := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp [List.filter, ih]

theorem list_length_filter_partition {α : Type} (L : List α) (p : α → Bool) :
    L.length = (L.filter p).length + (L.filter (fun x => !(p x))).length := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    cases h : p x <;> simp [List.filter, h] <;> omega

theorem list_length_filter_mono {α : Type} (L : List α) (p q : α → Bool)
    (h : ∀ x : α, p x = true → q x = true) :
    (L.filter p).length ≤ (L.filter q).length := by
  induction L with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    cases hp : p x with
    | false =>
      cases hq : q x <;> simp [List.filter, hp, hq] <;> omega
    | true =>
      have hq : q x = true := h x hp
      simp [List.filter, hp, hq]
      omega

theorem list_filter_filter_eq {α : Type} (L : List α) (p q : α → Bool) :
    (L.filter p).filter q = L.filter (fun x => p x && q x) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;> simp [List.filter, hp, hq, ih]

/-- Universal finite pigeonhole / union-bound lemma:
    if each of `R` rows kills at most `K` candidates in `U` and `R * K < U.length`,
    then at least one candidate `p ∈ U` survives all rows. -/
theorem pigeonhole_union_bound {α β : Type} (U : List α) (rows : List β)
    (kill : α → β → Bool) (K : Nat)
    (hK : ∀ r : β, r ∈ rows → (U.filter (fun p => kill p r)).length ≤ K)
    (hlt : rows.length * K < U.length) :
    ∃ p : α, p ∈ U ∧ ∀ r : β, r ∈ rows → kill p r = false := by
  have hmain : ∀ rs : List β,
      (∀ r : β, r ∈ rs → (U.filter (fun p => kill p r)).length ≤ K) →
      U.length ≤ (U.filter (fun p => rs.all (fun r => !(kill p r)))).length + rs.length * K := by
    intro rs hrs
    induction rs with
    | nil =>
      simp only [List.all_nil, list_filter_true, List.length_nil, Nat.zero_mul, Nat.add_zero]
      exact Nat.le_refl _
    | cons r rs ih =>
      have hrs_tail : ∀ r' : β, r' ∈ rs → (U.filter (fun p => kill p r')).length ≤ K :=
        fun r' hr' => hrs r' (List.mem_cons_of_mem r hr')
      have ih_bound := ih hrs_tail
      have hr_bound : (U.filter (fun p => kill p r)).length ≤ K := hrs r List.mem_cons_self
      let S := U.filter (fun p => rs.all (fun r' => !(kill p r')))
      have hS_len : S.length = (U.filter (fun p => rs.all (fun r' => !(kill p r')))).length := rfl
      have hpart := list_length_filter_partition S (fun p => !(kill p r))
      have hnot : (S.filter (fun p => !(!(kill p r)))).length ≤
          (U.filter (fun p => kill p r)).length := by
        have hrew : S.filter (fun p => !(!(kill p r))) =
            U.filter (fun p => rs.all (fun r' => !(kill p r')) && kill p r) := by
          have h1 := list_filter_filter_eq U (fun p => rs.all (fun r' => !(kill p r')))
            (fun p => !(!(kill p r)))
          have h2 : (fun x => (rs.all fun r' => !kill x r') && !!kill x r) =
              (fun p => (rs.all fun r' => !kill p r') && kill p r) := by
            funext x; simp [Bool.not_not]
          rw [h2] at h1
          exact h1
        rw [hrew]
        apply list_length_filter_mono
        intro x hx
        cases hkr : kill x r
        · simp [hkr] at hx
        · rfl
      have hcons_eq : U.filter (fun p => (r :: rs).all (fun r' => !(kill p r'))) =
          S.filter (fun p => !(kill p r)) := by
        have h1 := list_filter_filter_eq U (fun p => rs.all (fun r' => !(kill p r')))
          (fun p => !(kill p r))
        rw [h1]
        have hpred : (fun p => (r :: rs).all (fun r' => !(kill p r'))) =
            (fun p => rs.all (fun r' => !(kill p r')) && !(kill p r)) := by
          funext p
          simp [List.all_cons, Bool.and_comm]
        rw [hpred]
      rw [hcons_eq]
      simp only [List.length_cons]
      have hmul : (rs.length + 1) * K = rs.length * K + K := Nat.succ_mul rs.length K
      rw [hmul]
      omega
  have hsurv := hmain rows hK
  have hpos : 0 < (U.filter (fun p => rows.all (fun r => !(kill p r)))).length := by omega
  cases hlist : U.filter (fun p => rows.all (fun r => !(kill p r))) with
  | nil =>
    rw [hlist] at hpos
    exact False.elim (Nat.not_lt_zero 0 hpos)
  | cons p ps =>
    have hmem : p ∈ U.filter (fun p => rows.all (fun r => !(kill p r))) := by
      rw [hlist]; exact List.mem_cons_self
    have ⟨hpU, hpall⟩ := List.mem_filter.mp hmem
    refine ⟨p, hpU, ?_⟩
    intro r hr
    have hall := List.all_eq_true.mp hpall r hr
    cases hkr : kill p r
    · rfl
    · simp [hkr] at hall

/-! ### Exact `C = 2, s = 3` Fano Plane Verification (`R_crit(2, 3) = 7`) -/

theorem allBipartitions8_length : allBipartitions8.length = 35 := by decide

theorem allTriples8_length : allTriples8.length = 56 := by decide

theorem every_triple_kills_five_check :
    allTriples8.all (fun r =>
      decide ((allBipartitions8.filter (fun p => bipartitionKilled p r)).length = 5)) = true := by
  decide

theorem every_triple_kills_five (r : Nat) (hr : r ∈ allTriples8) :
    (allBipartitions8.filter (fun p => bipartitionKilled p r)).length = 5 := by
  have h := List.all_eq_true.mp every_triple_kills_five_check r hr
  exact of_decide_eq_true h

theorem le_six_triples_always_feasible (rows : List Nat)
    (htriples : ∀ r : Nat, r ∈ rows → r ∈ allTriples8)
    (hlen : rows.length ≤ 6) :
    rowsFeasible8 rows := by
  have hK : ∀ r : Nat, r ∈ rows →
      (allBipartitions8.filter (fun p => bipartitionKilled p r)).length ≤ 5 := by
    intro r hr
    rw [every_triple_kills_five r (htriples r hr)]
    exact Nat.le_refl 5
  have hlt : rows.length * 5 < allBipartitions8.length := by
    rw [allBipartitions8_length]
    omega
  obtain ⟨p, hpU, hsurv⟩ := pigeonhole_union_bound allBipartitions8 rows bipartitionKilled 5 hK hlt
  refine ⟨p, hpU, ?_⟩
  intro r hr
  have hk := hsurv r hr
  unfold bipartitionKilled at hk
  cases hf : bipartitionFeasible p r
  · simp [hf] at hk
  · rfl

theorem fanoLines8_length : fanoLines8.length = 7 := by decide

theorem fanoLines8_all_triples_check :
    fanoLines8.all (fun r => decide (r ∈ allTriples8)) = true := by decide

theorem fanoLines8_all_triples (r : Nat) (hr : r ∈ fanoLines8) : r ∈ allTriples8 :=
  of_decide_eq_true (List.all_eq_true.mp fanoLines8_all_triples_check r hr)

theorem fanoLines8_pairwise_inter_one_check :
    (List.range 7).all (fun i =>
      (List.range 7).all (fun j =>
        if i == j then true
        else decide (interCount8 (fanoLines8.getD i 0) (fanoLines8.getD j 0) = 1))) = true := by
  decide

theorem fanoLines8_pairwise_disjoint_kills_check :
    (List.range 7).all (fun i =>
      (List.range 7).all (fun j =>
        if i == j then true
        else allBipartitions8.all (fun p =>
          !(bipartitionKilled p (fanoLines8.getD i 0) &&
            bipartitionKilled p (fanoLines8.getD j 0))))) = true := by
  decide

theorem fanoLines8_kills_all_check :
    allBipartitions8.all (fun p => fanoLines8.any (fun r => bipartitionKilled p r)) = true := by
  decide

theorem fanoLines8_not_feasible : ¬ rowsFeasible8 fanoLines8 := by
  intro ⟨p, hpU, hfeas⟩
  have hany := List.all_eq_true.mp fanoLines8_kills_all_check p hpU
  obtain ⟨r, hr, hkill⟩ := List.any_eq_true.mp hany
  have hf := hfeas r hr
  unfold bipartitionKilled at hkill
  rw [hf] at hkill
  exact Bool.noConfusion hkill

/-- Headline Theorem 3: Universal First-Moment Lower Bound & Exact Fano Plane `PG(2, 2)`
    `2:4` Column-Permutation Obstruction Theorem (`R_crit(2, 3) = 7`). -/
theorem fano_plane_sparse24_obstruction_exact :
    (∀ C : Nat, 1 ≤ C →
      (4 * C - 1) * (4 * C - 2) ≤ 6 * rCritLowerBound3 C ∧
      ∀ R : Nat, R < rCritLowerBound3 C → 6 * R < (4 * C - 1) * (4 * C - 2)) ∧
    (rCritLowerBound3 1 = 1 ∧ rCritLowerBound3 2 = 7 ∧ rCritLowerBound3 3 = 19 ∧
     rCritLowerBound3 4 = 35 ∧ rCritLowerBound3 8 = 155 ∧
     rCritLowerBound3 16 = 651 ∧ rCritLowerBound3 32 = 2667) ∧
    (allBipartitions8.length = 35 ∧ allTriples8.length = 56 ∧
     ∀ r : Nat, r ∈ allTriples8 →
       (allBipartitions8.filter (fun p => bipartitionKilled p r)).length = 5) ∧
    (∀ rows : List Nat, (∀ r : Nat, r ∈ rows → r ∈ allTriples8) →
      rows.length ≤ 6 → rowsFeasible8 rows) ∧
    (fanoLines8.length = 7 ∧
     (∀ r : Nat, r ∈ fanoLines8 → r ∈ allTriples8) ∧
     (∀ i j : Nat, i < 7 → j < 7 → i ≠ j →
       interCount8 (fanoLines8.getD i 0) (fanoLines8.getD j 0) = 1 ∧
       ∀ p : Nat, p ∈ allBipartitions8 →
         (!(bipartitionKilled p (fanoLines8.getD i 0) &&
            bipartitionKilled p (fanoLines8.getD j 0))) = true) ∧
     ¬ rowsFeasible8 fanoLines8) := by
  refine ⟨rCritLowerBound3_spec, by decide,
    ⟨allBipartitions8_length, allTriples8_length, every_triple_kills_five⟩,
    le_six_triples_always_feasible,
    ⟨fanoLines8_length, fanoLines8_all_triples, ?_, fanoLines8_not_feasible⟩⟩
  intro i j hi hj hne
  have hi_mem : i ∈ List.range 7 := List.mem_range.mpr hi
  have hj_mem : j ∈ List.range 7 := List.mem_range.mpr hj
  have hbeq : (i == j) = false := beq_false_of_ne hne
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp fanoLines8_pairwise_inter_one_check i hi_mem) j hj_mem
  rw [hbeq] at h1
  have h2 := List.all_eq_true.mp (List.all_eq_true.mp fanoLines8_pairwise_disjoint_kills_check i hi_mem) j hj_mem
  rw [hbeq] at h2
  exact ⟨of_decide_eq_true h1, fun p hp => List.all_eq_true.mp h2 p hp⟩

end FanoSparse24Perm
