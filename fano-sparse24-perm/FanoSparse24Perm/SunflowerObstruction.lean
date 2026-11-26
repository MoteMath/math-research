/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FanoSparse24Perm.Defs

/-!
# Theorem 4: Exact 3-Column Sunflower `2:4` Obstruction (`R_crit(2, 4) = 4`)

Proves:
1. There are `70` weight-4 rows on `8` columns (`allQuads8.length = 70`), and every weight-4
   row kills exactly `17` of the `35` `(4, 4)`-bipartitions (so the naive union bound is
   `⌈35 / 17⌉ = 3`).
2. Despite the union bound of `3`, EVERY list of `≤ 3` weight-4 rows on `8` columns admits a
   `2:4`-feasible `(4, 4)`-bipartition (`rowsFeasible8 rows`), proved via exact `S_8` Venn-region
   canonicalization reducing `(r1, r2)` to `{15, 23, 51}` followed by exact kernel verification
   across all `3 × 70 = 210` canonical triples.
3. The `4` weight-4 sunflower rows (`sunflowerRows8`: core `{0, 1, 2}` with petals `3, 4, 5, 6`)
   kill all `35 / 35` `(4, 4)`-bipartitions simultaneously (`¬ rowsFeasible8 sunflowerRows8`),
   establishing `R_crit(2, 4) = 4` exactly.
-/

namespace FanoSparse24Perm

/-! ### Exact Counting for Weight-4 Rows on `8` Columns -/

theorem allQuads8_length : allQuads8.length = 70 := by decide

theorem every_quad_kills_seventeen_check :
    allQuads8.all (fun r =>
      decide ((allBipartitions8.filter (fun p => bipartitionKilled p r)).length = 17)) = true := by
  decide

theorem every_quad_kills_seventeen (r : Nat) (hr : r ∈ allQuads8) :
    (allBipartitions8.filter (fun p => bipartitionKilled p r)).length = 17 :=
  of_decide_eq_true (List.all_eq_true.mp every_quad_kills_seventeen_check r hr)

/-! ### `S_8` Venn-Region Canonicalization Machinery -/

def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

theorem listSum_append (xs ys : List Nat) : listSum (xs ++ ys) = listSum xs + listSum ys := by
  induction xs with
  | nil => simp [listSum]
  | cons x xs ih => simp [listSum, ih]; omega

theorem listSum_filter_partition (xs : List Nat) (p : Nat → Bool) (f : Nat → Nat) :
    listSum ((xs.filter p).map f) + listSum ((xs.filter (fun i => !(p i))).map f) =
      listSum (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x <;> simp [List.filter, List.map, listSum, hp] <;> omega

theorem list_filter_mem_iff {α : Type} (xs : List α) (p : α → Bool) (a : α) :
    a ∈ xs.filter p ↔ a ∈ xs ∧ p a = true :=
  List.mem_filter

theorem list_filter_and_comm (xs : List Nat) (p q : Nat → Bool) :
    (xs.filter p).filter q = xs.filter (fun i => p i && q i) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;> simp [List.filter, hp, hq, ih]

def orientRow (r1 r2 : Nat) : Nat :=
  if 2 ≤ interCount8 r1 r2 then r2 else 255 - r2

def permList (r1 r2 : Nat) : List Nat :=
  let r2' := orientRow r1 r2
  (List.range 8).filter (fun i => bitTest r1 i && bitTest r2' i) ++
  (List.range 8).filter (fun i => bitTest r1 i && !(bitTest r2' i)) ++
  (List.range 8).filter (fun i => !(bitTest r1 i) && bitTest r2' i) ++
  (List.range 8).filter (fun i => !(bitTest r1 i) && !(bitTest r2' i))

theorem listSum_permList (r1 r2 : Nat) (f : Nat → Nat) :
    listSum ((permList r1 r2).map f) = listSum ((List.range 8).map f) := by
  unfold permList
  simp only [List.map_append, listSum_append]
  have h1 : listSum (((List.range 8).filter (fun i => bitTest r1 i && bitTest (orientRow r1 r2) i)).map f) +
      listSum (((List.range 8).filter (fun i => bitTest r1 i && !(bitTest (orientRow r1 r2) i))).map f) =
      listSum (((List.range 8).filter (fun i => bitTest r1 i)).map f) := by
    rw [← list_filter_and_comm, ← list_filter_and_comm]
    exact listSum_filter_partition ((List.range 8).filter (fun i => bitTest r1 i)) (fun i => bitTest (orientRow r1 r2) i) f
  have h2 : listSum (((List.range 8).filter (fun i => !(bitTest r1 i) && bitTest (orientRow r1 r2) i)).map f) +
      listSum (((List.range 8).filter (fun i => !(bitTest r1 i) && !(bitTest (orientRow r1 r2) i))).map f) =
      listSum (((List.range 8).filter (fun i => !(bitTest r1 i))).map f) := by
    rw [← list_filter_and_comm, ← list_filter_and_comm]
    exact listSum_filter_partition ((List.range 8).filter (fun i => !(bitTest r1 i))) (fun i => bitTest (orientRow r1 r2) i) f
  have h3 := listSum_filter_partition (List.range 8) (fun i => bitTest r1 i) f
  omega

theorem listSum_map_const_one (xs : List Nat) : listSum (xs.map (fun _ => 1)) = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.map, listSum, ih]; omega

theorem permList_length (r1 r2 : Nat) : (permList r1 r2).length = 8 := by
  have h := listSum_permList r1 r2 (fun _ => 1)
  rw [listSum_map_const_one, listSum_map_const_one] at h
  exact h

theorem listSum_len8 (L : List Nat) (hL : L.length = 8) (f : Nat → Nat) :
    listSum (L.map f) =
      f (L.getD 0 0) + f (L.getD 1 0) + f (L.getD 2 0) + f (L.getD 3 0) +
      f (L.getD 4 0) + f (L.getD 5 0) + f (L.getD 6 0) + f (L.getD 7 0) := by
  match L, hL with
  | [a0, a1, a2, a3, a4, a5, a6, a7], _ =>
    simp [List.map, listSum, List.getD]
    omega

theorem listSum_range8 (f : Nat → Nat) :
    listSum ((List.range 8).map f) =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  have h := listSum_len8 (List.range 8) (by decide) f
  simpa [List.range, List.range.loop, List.getD] using h

def pullMask (L : List Nat) (m : Nat) : Nat :=
  (if bitTest m (L.getD 0 0) then 1 else 0) +
  (if bitTest m (L.getD 1 0) then 2 else 0) +
  (if bitTest m (L.getD 2 0) then 4 else 0) +
  (if bitTest m (L.getD 3 0) then 8 else 0) +
  (if bitTest m (L.getD 4 0) then 16 else 0) +
  (if bitTest m (L.getD 5 0) then 32 else 0) +
  (if bitTest m (L.getD 6 0) then 64 else 0) +
  (if bitTest m (L.getD 7 0) then 128 else 0)

def pushMask (L : List Nat) (q : Nat) : Nat :=
  (if bitTest q 0 then 2 ^ (L.getD 0 0) else 0) +
  (if bitTest q 1 then 2 ^ (L.getD 1 0) else 0) +
  (if bitTest q 2 then 2 ^ (L.getD 2 0) else 0) +
  (if bitTest q 3 then 2 ^ (L.getD 3 0) else 0) +
  (if bitTest q 4 then 2 ^ (L.getD 4 0) else 0) +
  (if bitTest q 5 then 2 ^ (L.getD 5 0) else 0) +
  (if bitTest q 6 then 2 ^ (L.getD 6 0) else 0) +
  (if bitTest q 7 then 2 ^ (L.getD 7 0) else 0)

def canonBipart (m : Nat) : Nat :=
  if bitTest m 0 then m else 255 - m

theorem pullMask_lt (L : List Nat) (m : Nat) : pullMask L m < 256 := by
  unfold pullMask
  cases bitTest m (L.getD 0 0) <;> cases bitTest m (L.getD 1 0) <;>
  cases bitTest m (L.getD 2 0) <;> cases bitTest m (L.getD 3 0) <;>
  cases bitTest m (L.getD 4 0) <;> cases bitTest m (L.getD 5 0) <;>
  cases bitTest m (L.getD 6 0) <;> cases bitTest m (L.getD 7 0) <;> decide

theorem bitTest_pullMask_gen (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    let m := (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
             (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0) +
             (if b6 then 64 else 0) + (if b7 then 128 else 0)
    bitTest m 0 = b0 ∧ bitTest m 1 = b1 ∧ bitTest m 2 = b2 ∧ bitTest m 3 = b3 ∧
    bitTest m 4 = b4 ∧ bitTest m 5 = b5 ∧ bitTest m 6 = b6 ∧ bitTest m 7 = b7 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
  cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> decide

theorem popcount8_pullMask (r1 r2 m : Nat) :
    popcount8 (pullMask (permList r1 r2) m) = popcount8 m := by
  let L := permList r1 r2
  have hbits := bitTest_pullMask_gen
    (bitTest m (L.getD 0 0)) (bitTest m (L.getD 1 0)) (bitTest m (L.getD 2 0)) (bitTest m (L.getD 3 0))
    (bitTest m (L.getD 4 0)) (bitTest m (L.getD 5 0)) (bitTest m (L.getD 6 0)) (bitTest m (L.getD 7 0))
  unfold popcount8 pullMask
  dsimp only [L] at hbits
  rw [hbits.1, hbits.2.1, hbits.2.2.1, hbits.2.2.2.1,
      hbits.2.2.2.2.1, hbits.2.2.2.2.2.1, hbits.2.2.2.2.2.2.1, hbits.2.2.2.2.2.2.2]
  have h1 := listSum_len8 (permList r1 r2) (permList_length r1 r2) (fun i => if bitTest m i then 1 else 0)
  have h2 := listSum_permList r1 r2 (fun i => if bitTest m i then 1 else 0)
  have h3 := listSum_range8 (fun i => if bitTest m i then 1 else 0)
  omega

theorem pullMask_in_allQuads8 {r1 r2 r3 : Nat} (hr3 : r3 ∈ allQuads8) :
    pullMask (permList r1 r2) r3 ∈ allQuads8 := by
  have hmem := List.mem_filter.mp hr3
  have hpop : popcount8 r3 = 4 := of_decide_eq_true hmem.2
  apply List.mem_filter.mpr
  refine ⟨List.mem_range.mpr (pullMask_lt (permList r1 r2) r3), ?_⟩
  rw [popcount8_pullMask, hpop]
  rfl

def idxOf : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, k => if x == k then 0 else 1 + idxOf xs k

theorem nodup_filter_append {xs : List Nat} (hnd : xs.Nodup) (p : Nat → Bool) :
    (xs.filter p ++ xs.filter (fun i => !(p i))).Nodup := by
  have h1 : (xs.filter p).Nodup := hnd.filter p
  have h2 : (xs.filter (fun i => !(p i))).Nodup := hnd.filter (fun i => !(p i))
  rw [List.nodup_append]
  refine ⟨h1, h2, ?_⟩
  intro a ha b hb hab
  subst hab
  have hp1 := (List.mem_filter.mp ha).2
  have hp2 := (List.mem_filter.mp hb).2
  rw [hp1] at hp2
  exact Bool.noConfusion hp2

theorem permList_nodup (r1 r2 : Nat) : (permList r1 r2).Nodup := by
  unfold permList
  let r2' := orientRow r1 r2
  have hrange : (List.range 8).Nodup := List.nodup_range
  have hstep1 : ((List.range 8).filter (fun i => bitTest r1 i) ++
      (List.range 8).filter (fun i => !(bitTest r1 i))).Nodup :=
    nodup_filter_append hrange (fun i => bitTest r1 i)
  have hL1 : ((List.range 8).filter (fun i => bitTest r1 i)).Nodup := hrange.filter _
  have hL2 : ((List.range 8).filter (fun i => !(bitTest r1 i))).Nodup := hrange.filter _
  have hA : ((List.range 8).filter (fun i => bitTest r1 i && bitTest r2' i) ++
      (List.range 8).filter (fun i => bitTest r1 i && !(bitTest r2' i))).Nodup := by
    rw [← list_filter_and_comm, ← list_filter_and_comm]
    exact nodup_filter_append hL1 (fun i => bitTest r2' i)
  have hB : ((List.range 8).filter (fun i => !(bitTest r1 i) && bitTest r2' i) ++
      (List.range 8).filter (fun i => !(bitTest r1 i) && !(bitTest r2' i))).Nodup := by
    rw [← list_filter_and_comm, ← list_filter_and_comm]
    exact nodup_filter_append hL2 (fun i => bitTest r2' i)
  have hassoc :
      ((List.range 8).filter (fun i => bitTest r1 i && bitTest r2' i) ++
       (List.range 8).filter (fun i => bitTest r1 i && !(bitTest r2' i)) ++
       (List.range 8).filter (fun i => !(bitTest r1 i) && bitTest r2' i) ++
       (List.range 8).filter (fun i => !(bitTest r1 i) && !(bitTest r2' i))) =
      ((List.range 8).filter (fun i => bitTest r1 i && bitTest r2' i) ++
       (List.range 8).filter (fun i => bitTest r1 i && !(bitTest r2' i))) ++
      ((List.range 8).filter (fun i => !(bitTest r1 i) && bitTest r2' i) ++
       (List.range 8).filter (fun i => !(bitTest r1 i) && !(bitTest r2' i))) := by
    simp [List.append_assoc]
  rw [hassoc, List.nodup_append]
  refine ⟨hA, hB, ?_⟩
  intro a ha b hb hab
  subst hab
  have ha1 : bitTest r1 a = true := by
    rcases List.mem_append.mp ha with h | h
    · exact ((Bool.and_eq_true _ _).mp (List.mem_filter.mp h).2).1
    · exact ((Bool.and_eq_true _ _).mp (List.mem_filter.mp h).2).1
  have hb1 : (!(bitTest r1 a)) = true := by
    rcases List.mem_append.mp hb with h | h
    · exact ((Bool.and_eq_true _ _).mp (List.mem_filter.mp h).2).1
    · exact ((Bool.and_eq_true _ _).mp (List.mem_filter.mp h).2).1
  rw [ha1] at hb1
  exact Bool.noConfusion hb1

theorem permList_lt8 (r1 r2 : Nat) : ∀ x : Nat, x ∈ permList r1 r2 → x < 8 := by
  intro x hx
  unfold permList at hx
  rcases List.mem_append.mp hx with h123 | h4
  · rcases List.mem_append.mp h123 with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · exact List.mem_range.mp (List.mem_filter.mp h1).1
      · exact List.mem_range.mp (List.mem_filter.mp h2).1
    · exact List.mem_range.mp (List.mem_filter.mp h3).1
  · exact List.mem_range.mp (List.mem_filter.mp h4).1

theorem idxOf_getD {L : List Nat} (hnd : L.Nodup) (j : Nat) (hj : j < L.length) :
    idxOf L (L.getD j 0) = j := by
  induction L generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    have ⟨hx_notin, hxs_nd⟩ := List.nodup_cons.mp hnd
    cases j with
    | zero => simp [List.getD, idxOf]
    | succ j =>
      simp only [List.getD, List.getElem?_cons_succ] at *
      have hj' : j < xs.length := by simp at hj; omega
      have hmem : xs.getD j 0 ∈ xs := by
        have : xs[j]? = some (xs[j]'hj') := List.getElem?_eq_getElem hj'
        simp only [List.getD, this, Option.getD_some]
        exact List.getElem_mem hj'
      have hne : x ≠ xs.getD j 0 := fun heq => hx_notin (heq ▸ hmem)
      simp only [List.getD] at hne
      simp only [idxOf, beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte]
      have hrec := ih hxs_nd j hj'
      omega

theorem interCount8_pushMask (r1 r2 q m : Nat) :
    pushMask (permList r1 r2) q < 256 ∧
    popcount8 (pushMask (permList r1 r2) q) = popcount8 q ∧
    interCount8 (pushMask (permList r1 r2) q) m = interCount8 q (pullMask (permList r1 r2) m) := by
  let L := permList r1 r2
  have hlen : L.length = 8 := permList_length r1 r2
  have hnd : L.Nodup := permList_nodup r1 r2
  let c : Nat → Bool := fun k => bitTest q (idxOf L k)
  have hc_getD : ∀ j : Nat, j < 8 → c (L.getD j 0) = bitTest q j := by
    intro j hj
    dsimp only [c]
    rw [idxOf_getD hnd j (by omega)]
  have hpm_eq : pushMask L q =
      (if c 0 then 1 else 0) + (if c 1 then 2 else 0) + (if c 2 then 4 else 0) +
      (if c 3 then 8 else 0) + (if c 4 then 16 else 0) + (if c 5 then 32 else 0) +
      (if c 6 then 64 else 0) + (if c 7 then 128 else 0) := by
    have h1 := listSum_len8 L hlen (fun k => if c k then 2 ^ k else 0)
    have h2 := listSum_permList r1 r2 (fun k => if c k then 2 ^ k else 0)
    have h3 := listSum_range8 (fun k => if c k then 2 ^ k else 0)
    rw [hc_getD 0 (by decide), hc_getD 1 (by decide), hc_getD 2 (by decide), hc_getD 3 (by decide),
        hc_getD 4 (by decide), hc_getD 5 (by decide), hc_getD 6 (by decide), hc_getD 7 (by decide)] at h1
    unfold pushMask
    change _ = _
    have h2' : listSum (L.map (fun k => if c k then 2 ^ k else 0)) =
        listSum ((List.range 8).map (fun k => if c k then 2 ^ k else 0)) := h2
    rw [h1, h3] at h2'
    simpa using h2'
  have hbits := bitTest_pullMask_gen (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7)
  have hlt : pushMask L q < 256 := by
    rw [hpm_eq]
    cases c 0 <;> cases c 1 <;> cases c 2 <;> cases c 3 <;>
    cases c 4 <;> cases c 5 <;> cases c 6 <;> cases c 7 <;> decide
  have hbit_k : ∀ k : Nat, k < 8 → bitTest (pushMask L q) k = c k := by
    intro k hk
    rw [hpm_eq]
    match k with
    | 0 => exact hbits.1
    | 1 => exact hbits.2.1
    | 2 => exact hbits.2.2.1
    | 3 => exact hbits.2.2.2.1
    | 4 => exact hbits.2.2.2.2.1
    | 5 => exact hbits.2.2.2.2.2.1
    | 6 => exact hbits.2.2.2.2.2.2.1
    | 7 => exact hbits.2.2.2.2.2.2.2
    | n + 8 => omega
  have hgetD_lt : ∀ j : Nat, j < 8 → L.getD j 0 < 8 := by
    intro j hj
    have hj' : j < L.length := by omega
    have hmem : L.getD j 0 ∈ L := by
      have : L[j]? = some (L[j]'hj') := List.getElem?_eq_getElem hj'
      simp only [List.getD, this, Option.getD_some]
      exact List.getElem_mem hj'
    exact permList_lt8 r1 r2 _ hmem
  have hbit_getD : ∀ j : Nat, j < 8 → bitTest (pushMask L q) (L.getD j 0) = bitTest q j := by
    intro j hj
    rw [hbit_k (L.getD j 0) (hgetD_lt j hj), hc_getD j hj]
  refine ⟨hlt, ?_, ?_⟩
  · have h1 := listSum_permList r1 r2 (fun i => if bitTest (pushMask L q) i then 1 else 0)
    have h2 := listSum_len8 L hlen (fun i => if bitTest (pushMask L q) i then 1 else 0)
    have h3 := listSum_range8 (fun i => if bitTest (pushMask L q) i then 1 else 0)
    rw [hbit_getD 0 (by decide), hbit_getD 1 (by decide), hbit_getD 2 (by decide), hbit_getD 3 (by decide),
        hbit_getD 4 (by decide), hbit_getD 5 (by decide), hbit_getD 6 (by decide), hbit_getD 7 (by decide)] at h2
    dsimp only [L] at h1 h2 h3
    unfold popcount8
    omega
  · have h1 := listSum_permList r1 r2 (fun i => if bitTest (pushMask L q) i && bitTest m i then 1 else 0)
    have h2 := listSum_len8 L hlen (fun i => if bitTest (pushMask L q) i && bitTest m i then 1 else 0)
    have h3 := listSum_range8 (fun i => if bitTest (pushMask L q) i && bitTest m i then 1 else 0)
    rw [hbit_getD 0 (by decide), hbit_getD 1 (by decide), hbit_getD 2 (by decide), hbit_getD 3 (by decide),
        hbit_getD 4 (by decide), hbit_getD 5 (by decide), hbit_getD 6 (by decide), hbit_getD 7 (by decide)] at h2
    have hpull := bitTest_pullMask_gen
      (bitTest m (L.getD 0 0)) (bitTest m (L.getD 1 0)) (bitTest m (L.getD 2 0)) (bitTest m (L.getD 3 0))
      (bitTest m (L.getD 4 0)) (bitTest m (L.getD 5 0)) (bitTest m (L.getD 6 0)) (bitTest m (L.getD 7 0))
    dsimp only [L] at h1 h2 h3 hpull
    unfold interCount8 pullMask
    rw [hpull.1, hpull.2.1, hpull.2.2.1, hpull.2.2.2.1,
        hpull.2.2.2.2.1, hpull.2.2.2.2.2.1, hpull.2.2.2.2.2.2.1, hpull.2.2.2.2.2.2.2]
    omega

theorem bit_comp_pair (a b : Bool) :
    (if a && !b then 1 else 0) + (if a && b then 1 else 0) = (if a then 1 else 0) := by
  cases a <;> cases b <;> rfl

theorem bitTest_comp {m i : Nat} (hm : m < 256) (hi : i < 8) :
    bitTest (255 - m) i = !(bitTest m i) := by
  unfold bitTest
  match i with
  | 0 => have : ((255 - m) / 2 ^ 0) % 2 + (m / 2 ^ 0) % 2 = 1 := by omega
         cases h : (m / 2 ^ 0) % 2 == 1 <;> simp_all <;> omega
  | 1 => have : ((255 - m) / 2 ^ 1) % 2 + (m / 2 ^ 1) % 2 = 1 := by omega
         cases h : (m / 2 ^ 1) % 2 == 1 <;> simp_all <;> omega
  | 2 => have : ((255 - m) / 2 ^ 2) % 2 + (m / 2 ^ 2) % 2 = 1 := by omega
         cases h : (m / 2 ^ 2) % 2 == 1 <;> simp_all <;> omega
  | 3 => have : ((255 - m) / 2 ^ 3) % 2 + (m / 2 ^ 3) % 2 = 1 := by omega
         cases h : (m / 2 ^ 3) % 2 == 1 <;> simp_all <;> omega
  | 4 => have : ((255 - m) / 2 ^ 4) % 2 + (m / 2 ^ 4) % 2 = 1 := by omega
         cases h : (m / 2 ^ 4) % 2 == 1 <;> simp_all <;> omega
  | 5 => have : ((255 - m) / 2 ^ 5) % 2 + (m / 2 ^ 5) % 2 = 1 := by omega
         cases h : (m / 2 ^ 5) % 2 == 1 <;> simp_all <;> omega
  | 6 => have : ((255 - m) / 2 ^ 6) % 2 + (m / 2 ^ 6) % 2 = 1 := by omega
         cases h : (m / 2 ^ 6) % 2 == 1 <;> simp_all <;> omega
  | 7 => have : ((255 - m) / 2 ^ 7) % 2 + (m / 2 ^ 7) % 2 = 1 := by omega
         cases h : (m / 2 ^ 7) % 2 == 1 <;> simp_all <;> omega
  | _ + 8 => omega

theorem interCount8_comp_right {a b : Nat} (hb : b < 256) :
    interCount8 a (255 - b) + interCount8 a b = popcount8 a := by
  unfold interCount8 popcount8
  rw [bitTest_comp hb (by decide), bitTest_comp hb (by decide),
      bitTest_comp hb (by decide), bitTest_comp hb (by decide),
      bitTest_comp hb (by decide), bitTest_comp hb (by decide),
      bitTest_comp hb (by decide), bitTest_comp hb (by decide)]
  have h0 := bit_comp_pair (bitTest a 0) (bitTest b 0)
  have h1 := bit_comp_pair (bitTest a 1) (bitTest b 1)
  have h2 := bit_comp_pair (bitTest a 2) (bitTest b 2)
  have h3 := bit_comp_pair (bitTest a 3) (bitTest b 3)
  have h4 := bit_comp_pair (bitTest a 4) (bitTest b 4)
  have h5 := bit_comp_pair (bitTest a 5) (bitTest b 5)
  have h6 := bit_comp_pair (bitTest a 6) (bitTest b 6)
  have h7 := bit_comp_pair (bitTest a 7) (bitTest b 7)
  omega

theorem interCount8_comm (a b : Nat) : interCount8 a b = interCount8 b a := by
  unfold interCount8
  simp only [Bool.and_comm]

theorem interCount8_comp_left {a b : Nat} (ha : a < 256) :
    interCount8 (255 - a) b + interCount8 a b = popcount8 b := by
  rw [interCount8_comm (255 - a) b, interCount8_comm a b]
  exact interCount8_comp_right ha

theorem popcount8_comp {m : Nat} (hm : m < 256) :
    popcount8 (255 - m) + popcount8 m = 8 := by
  unfold popcount8
  rw [bitTest_comp hm (by decide), bitTest_comp hm (by decide),
      bitTest_comp hm (by decide), bitTest_comp hm (by decide),
      bitTest_comp hm (by decide), bitTest_comp hm (by decide),
      bitTest_comp hm (by decide), bitTest_comp hm (by decide)]
  have hpair : ∀ b : Bool, (if !b then 1 else 0) + (if b then 1 else 0) = 1 := by
    intro b; cases b <;> rfl
  have h0 := hpair (bitTest m 0)
  have h1 := hpair (bitTest m 1)
  have h2 := hpair (bitTest m 2)
  have h3 := hpair (bitTest m 3)
  have h4 := hpair (bitTest m 4)
  have h5 := hpair (bitTest m 5)
  have h6 := hpair (bitTest m 6)
  have h7 := hpair (bitTest m 7)
  omega

theorem canonBipart_mem {p : Nat} (hp : p ∈ allQuads8) : canonBipart p ∈ allBipartitions8 := by
  have hlt : p < 256 := List.mem_range.mp (List.mem_filter.mp hp).1
  have hpop : popcount8 p = 4 := of_decide_eq_true (List.mem_filter.mp hp).2
  unfold canonBipart
  by_cases h0 : bitTest p 0 = true
  · simp only [h0, ↓reduceIte]
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr hlt, ?_⟩
    unfold isBipartition8
    simp [hlt, h0, hpop]
  · have h0f : bitTest p 0 = false := by cases hb : bitTest p 0 <;> simp_all
    simp only [h0f]
    have hc_lt : 255 - p < 256 := by omega
    have hc_0 : bitTest (255 - p) 0 = true := by rw [bitTest_comp hlt (by decide), h0f]; rfl
    have hc_pop : popcount8 (255 - p) = 4 := by have := popcount8_comp hlt; omega
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr hc_lt, ?_⟩
    unfold isBipartition8
    simp [hc_lt, hc_0, hc_pop]

theorem canonBipart_feasible_eq {p r : Nat} (hp : p ∈ allQuads8) (hr : r ∈ allQuads8) :
    bipartitionFeasible (canonBipart p) r = bipartitionFeasible p r := by
  have hlt : p < 256 := List.mem_range.mp (List.mem_filter.mp hp).1
  have hr_pop : popcount8 r = 4 := of_decide_eq_true (List.mem_filter.mp hr).2
  unfold canonBipart
  by_cases h0 : bitTest p 0 = true
  · simp [h0]
  · have h0f : bitTest p 0 = false := by cases hb : bitTest p 0 <;> simp_all
    simp only [h0f, Bool.false_eq_true, ↓reduceIte]
    unfold bipartitionFeasible
    have hsum := interCount8_comp_left (b := r) hlt
    rw [hr_pop] at hsum ⊢
    by_cases h : interCount8 p r = 2
    · have hc : interCount8 (255 - p) r = 2 := by omega
      simp [h, hc]
    · have hc1 : ¬ (interCount8 p r ≤ 2 ∧ 4 - interCount8 p r ≤ 2) := by omega
      have hc2 : ¬ (interCount8 (255 - p) r ≤ 2 ∧ 4 - interCount8 (255 - p) r ≤ 2) := by omega
      rw [decide_eq_false hc1, decide_eq_false hc2]

theorem comp_quad_feasible_eq {p r : Nat} (hp : popcount8 p = 4) (hr : r ∈ allQuads8) :
    bipartitionFeasible p (255 - r) = bipartitionFeasible p r := by
  have hr_lt : r < 256 := List.mem_range.mp (List.mem_filter.mp hr).1
  have hr_pop : popcount8 r = 4 := of_decide_eq_true (List.mem_filter.mp hr).2
  have hrc_pop : popcount8 (255 - r) = 4 := by have := popcount8_comp hr_lt; omega
  have hsum := interCount8_comp_right (a := p) hr_lt
  rw [hp] at hsum
  unfold bipartitionFeasible
  rw [hr_pop, hrc_pop]
  by_cases h : interCount8 p r = 2
  · have hc : interCount8 p (255 - r) = 2 := by omega
    simp [h, hc]
  · have hc1 : ¬ (interCount8 p r ≤ 2 ∧ 4 - interCount8 p r ≤ 2) := by omega
    have hc2 : ¬ (interCount8 p (255 - r) ≤ 2 ∧ 4 - interCount8 p (255 - r) ≤ 2) := by omega
    rw [decide_eq_false hc1, decide_eq_false hc2]

theorem pullMask_r1_r2_canonical (r1 r2 : Nat) (hr1 : r1 ∈ allQuads8) (hr2 : r2 ∈ allQuads8) :
    pullMask (permList r1 r2) r1 = 15 ∧
    (pullMask (permList r1 r2) (orientRow r1 r2) = 15 ∨
     pullMask (permList r1 r2) (orientRow r1 r2) = 23 ∨
     pullMask (permList r1 r2) (orientRow r1 r2) = 51) := by
  have hr1_pop : popcount8 r1 = 4 := of_decide_eq_true (List.mem_filter.mp hr1).2
  have hr2_pop : popcount8 r2 = 4 := of_decide_eq_true (List.mem_filter.mp hr2).2
  have hr2_lt : r2 < 256 := List.mem_range.mp (List.mem_filter.mp hr2).1
  let r2' := orientRow r1 r2
  have hcomp_pop : popcount8 (255 - r2) = 4 ∧ interCount8 r1 (255 - r2) + interCount8 r1 r2 = 4 := by
    have h1 := popcount8_comp hr2_lt
    have h2 := interCount8_comp_right (a := r1) hr2_lt
    omega
  -- Lengths of the 4 blocks
  let A := (List.range 8).filter (fun i => bitTest r1 i && bitTest r2' i)
  let B := (List.range 8).filter (fun i => bitTest r1 i && !(bitTest r2' i))
  let C := (List.range 8).filter (fun i => !(bitTest r1 i) && bitTest r2' i)
  let D := (List.range 8).filter (fun i => !(bitTest r1 i) && !(bitTest r2' i))
  have hpop_eq : ∀ m : Nat, ((List.range 8).filter (fun i => bitTest m i)).length = popcount8 m := by
    intro m
    have h2 : ∀ xs : List Nat, (xs.filter (fun i => bitTest m i)).length =
        listSum (xs.map (fun i => if bitTest m i then 1 else 0)) := by
      intro xs; induction xs with
      | nil => rfl
      | cons x xs ih =>
        cases h : bitTest m x <;> simp [List.filter, List.map, listSum, h, ih] <;> omega
    rw [h2, listSum_range8]; unfold popcount8; omega
  have hinter_eq : ∀ a b : Nat,
      ((List.range 8).filter (fun i => bitTest a i && bitTest b i)).length = interCount8 a b := by
    intro a b
    have h2 : ∀ xs : List Nat, (xs.filter (fun i => bitTest a i && bitTest b i)).length =
        listSum (xs.map (fun i => if bitTest a i && bitTest b i then 1 else 0)) := by
      intro xs; induction xs with
      | nil => rfl
      | cons x xs ih =>
        cases h : (bitTest a x && bitTest b x) <;> simp [List.filter, List.map, listSum, h, ih] <;> omega
    rw [h2, listSum_range8]; unfold interCount8; omega
  have hAB_len : A.length + B.length = 4 := by
    have h1 := listSum_filter_partition ((List.range 8).filter (fun i => bitTest r1 i)) (fun i => bitTest r2' i) (fun _ => 1)
    rw [list_filter_and_comm, list_filter_and_comm, listSum_map_const_one, listSum_map_const_one, listSum_map_const_one] at h1
    have h2 := hpop_eq r1
    dsimp only [A, B]
    omega
  have hAC_len : A.length + C.length = 4 := by
    have hr2'_pop : popcount8 r2' = 4 := by
      dsimp only [r2', orientRow]
      by_cases h : 2 ≤ interCount8 r1 r2 <;> simp [h, hr2_pop, hcomp_pop.1]
    have h1 := listSum_filter_partition ((List.range 8).filter (fun i => bitTest r2' i)) (fun i => bitTest r1 i) (fun _ => 1)
    rw [list_filter_and_comm, list_filter_and_comm, listSum_map_const_one, listSum_map_const_one, listSum_map_const_one] at h1
    have hA' : ((List.range 8).filter (fun i => bitTest r2' i && bitTest r1 i)).length = A.length := by
      have : (fun i => bitTest r2' i && bitTest r1 i) = (fun i => bitTest r1 i && bitTest r2' i) := by
        funext i; exact Bool.and_comm _ _
      rw [this]
    have hC' : ((List.range 8).filter (fun i => bitTest r2' i && !(bitTest r1 i))).length = C.length := by
      have : (fun i => bitTest r2' i && !(bitTest r1 i)) = (fun i => !(bitTest r1 i) && bitTest r2' i) := by
        funext i; exact Bool.and_comm _ _
      rw [this]
    rw [hA', hC', hpop_eq r2', hr2'_pop] at h1
    exact h1
  have hA_ge2 : 2 ≤ A.length := by
    have hA_eq : A.length = interCount8 r1 r2' := hinter_eq r1 r2'
    rw [hA_eq]
    dsimp only [r2', orientRow]
    by_cases h : 2 ≤ interCount8 r1 r2
    · simp [h]
    · simp [h]; omega
  have hA_le4 : A.length ≤ 4 := by omega
  -- Helper: getD on concatenated blocks
  have getD_mem : ∀ (xs : List Nat) (j : Nat), j < xs.length → xs.getD j 0 ∈ xs := by
    intro xs j hj
    induction xs generalizing j with
    | nil => simp at hj
    | cons x xs ih =>
      cases j with
      | zero => simp [List.getD]
      | succ j =>
        simp only [List.getD, List.getElem?_cons_succ]
        exact List.mem_cons_of_mem x (ih j (by simp at hj; omega))
  have getD_append_left : ∀ (xs ys : List Nat) (j : Nat), j < xs.length →
      (xs ++ ys).getD j 0 = xs.getD j 0 := by
    intro xs ys j hj
    simp only [List.getD, List.getElem?_append_left hj]
  have getD_append_right : ∀ (xs ys : List Nat) (j : Nat), xs.length ≤ j →
      (xs ++ ys).getD j 0 = ys.getD (j - xs.length) 0 := by
    intro xs ys j hj
    simp only [List.getD, List.getElem?_append_right hj]
  have hL_eq : permList r1 r2 = ((A ++ B) ++ (C ++ D)) := by
    unfold permList
    dsimp only [A, B, C, D, r2']
    simp [List.append_assoc]
  have hCD_len : C.length + D.length = 4 := by
    have h8 := permList_length r1 r2
    rw [hL_eq] at h8
    simp only [List.length_append] at h8
    omega
  have h_r1_true : ∀ j : Nat, j < 4 → bitTest r1 ((permList r1 r2).getD j 0) = true := by
    intro j hj
    rw [hL_eq, getD_append_left (A ++ B) (C ++ D) j (by simp; omega)]
    have hmem := getD_mem (A ++ B) j (by simp; omega)
    rcases List.mem_append.mp hmem with hA | hB
    · exact (Bool.and_eq_true _ _).mp (List.mem_filter.mp hA).2 |>.1
    · exact (Bool.and_eq_true _ _).mp (List.mem_filter.mp hB).2 |>.1
  have h_r1_false : ∀ j : Nat, 4 ≤ j → j < 8 → bitTest r1 ((permList r1 r2).getD j 0) = false := by
    intro j hj1 hj2
    rw [hL_eq, getD_append_right (A ++ B) (C ++ D) j (by simp; omega)]
    have hmem := getD_mem (C ++ D) (j - (A ++ B).length) (by simp; omega)
    rcases List.mem_append.mp hmem with hC | hD
    · have h := (Bool.and_eq_true _ _).mp (List.mem_filter.mp hC).2 |>.1
      cases hb : bitTest r1 ((C ++ D).getD (j - (A ++ B).length) 0)
      · rfl
      · rw [hb] at h; exact Bool.noConfusion h
    · have h := (Bool.and_eq_true _ _).mp (List.mem_filter.mp hD).2 |>.1
      cases hb : bitTest r1 ((C ++ D).getD (j - (A ++ B).length) 0)
      · rfl
      · rw [hb] at h; exact Bool.noConfusion h
  have h_r2_bit : ∀ j : Nat, j < 8 →
      bitTest r2' ((permList r1 r2).getD j 0) =
        (decide (j < A.length) || decide (4 ≤ j ∧ j < 4 + C.length)) := by
    intro j hj
    rw [hL_eq]
    by_cases h4 : j < 4
    · rw [getD_append_left (A ++ B) (C ++ D) j (by simp; omega)]
      by_cases hA : j < A.length
      · rw [getD_append_left A B j hA]
        have hmem := getD_mem A j hA
        have ht := (Bool.and_eq_true _ _).mp (List.mem_filter.mp hmem).2 |>.2
        rw [ht]; simp [hA]
      · rw [getD_append_right A B j (by omega)]
        have hmem := getD_mem B (j - A.length) (by omega)
        have hf := (Bool.and_eq_true _ _).mp (List.mem_filter.mp hmem).2 |>.2
        have hnot4 : ¬ (4 ≤ j ∧ j < 4 + C.length) := by omega
        have hbf : bitTest r2' (B.getD (j - A.length) 0) = false := by
          cases hb : bitTest r2' (B.getD (j - A.length) 0)
          · rfl
          · rw [hb] at hf; exact Bool.noConfusion hf
        rw [hbf]; simp [hA, hnot4]
    · rw [getD_append_right (A ++ B) (C ++ D) j (by simp; omega)]
      have hsub : (A ++ B).length = 4 := by simp; omega
      rw [hsub]
      by_cases hC : j - 4 < C.length
      · rw [getD_append_left C D (j - 4) hC]
        have hmem := getD_mem C (j - 4) hC
        have ht := (Bool.and_eq_true _ _).mp (List.mem_filter.mp hmem).2 |>.2
        have hcond : 4 ≤ j ∧ j < 4 + C.length := by omega
        rw [ht]; simp [hcond]
      · rw [getD_append_right C D (j - 4) (by omega)]
        have hmem := getD_mem D (j - 4 - C.length) (by omega)
        have hf := (Bool.and_eq_true _ _).mp (List.mem_filter.mp hmem).2 |>.2
        have hnotA : ¬ j < A.length := by omega
        have hnotC : ¬ (4 ≤ j ∧ j < 4 + C.length) := by omega
        have hbf : bitTest r2' (D.getD (j - 4 - C.length) 0) = false := by
          cases hb : bitTest r2' (D.getD (j - 4 - C.length) 0)
          · rfl
          · rw [hb] at hf; exact Bool.noConfusion hf
        rw [hbf]; simp [hnotA, hnotC]
  constructor
  · unfold pullMask
    rw [h_r1_true 0 (by decide), h_r1_true 1 (by decide), h_r1_true 2 (by decide), h_r1_true 3 (by decide),
        h_r1_false 4 (by decide) (by decide), h_r1_false 5 (by decide) (by decide),
        h_r1_false 6 (by decide) (by decide), h_r1_false 7 (by decide) (by decide)]
    rfl
  · unfold pullMask
    rw [h_r2_bit 0 (by decide), h_r2_bit 1 (by decide), h_r2_bit 2 (by decide), h_r2_bit 3 (by decide),
        h_r2_bit 4 (by decide), h_r2_bit 5 (by decide), h_r2_bit 6 (by decide), h_r2_bit 7 (by decide)]
    have hcases : (A.length = 4 ∧ C.length = 0) ∨ (A.length = 3 ∧ C.length = 1) ∨ (A.length = 2 ∧ C.length = 2) := by
      omega
    rcases hcases with ⟨hA, hC⟩ | ⟨hA, hC⟩ | ⟨hA, hC⟩
    · left; rw [hA, hC]; rfl
    · right; left; rw [hA, hC]; rfl
    · right; right; rw [hA, hC]; rfl

theorem canonical_triples_feasible_check :
    ([15, 23, 51]).all (fun c =>
      allQuads8.all (fun r3 =>
        allBipartitions8.any (fun q =>
          bipartitionFeasible q 15 && bipartitionFeasible q c && bipartitionFeasible q r3))) = true := by
  decide

theorem three_quads_always_feasible (r1 r2 r3 : Nat)
    (hr1 : r1 ∈ allQuads8) (hr2 : r2 ∈ allQuads8) (hr3 : r3 ∈ allQuads8) :
    rowsFeasible8 [r1, r2, r3] := by
  let L := permList r1 r2
  have ⟨hp1, hp2⟩ := pullMask_r1_r2_canonical r1 r2 hr1 hr2
  have hr3' : pullMask L r3 ∈ allQuads8 := pullMask_in_allQuads8 hr3
  have hc_mem : pullMask L (orientRow r1 r2) ∈ [15, 23, 51] := by
    rcases hp2 with h | h | h <;> rw [h] <;> decide
  have hany := List.all_eq_true.mp
    (List.all_eq_true.mp canonical_triples_feasible_check (pullMask L (orientRow r1 r2)) hc_mem)
    (pullMask L r3) hr3'
  obtain ⟨q, hq_mem, hq_feas⟩ := List.any_eq_true.mp hany
  have hf1 : bipartitionFeasible q 15 = true :=
    ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hq_feas).1).1
  have hf2 : bipartitionFeasible q (pullMask L (orientRow r1 r2)) = true :=
    ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hq_feas).1).2
  have hf3 : bipartitionFeasible q (pullMask L r3) = true :=
    ((Bool.and_eq_true _ _).mp hq_feas).2
  have hq_pop : popcount8 q = 4 := by
    have := (List.mem_filter.mp hq_mem).2
    unfold isBipartition8 at this
    exact of_decide_eq_true ((Bool.and_eq_true _ _).mp this).2
  let p0 := pushMask L q
  have ⟨hp0_lt, hp0_pop, _⟩ := interCount8_pushMask r1 r2 q r1
  have hp0_quad : p0 ∈ allQuads8 := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr hp0_lt, ?_⟩
    rw [hp0_pop, hq_pop]; rfl
  have hcanon_mem : canonBipart p0 ∈ allBipartitions8 := canonBipart_mem hp0_quad
  have hcanon_pop : popcount8 (canonBipart p0) = 4 := by
    have := (List.mem_filter.mp hcanon_mem).2
    unfold isBipartition8 at this
    exact of_decide_eq_true ((Bool.and_eq_true _ _).mp this).2
  have hcanon_eq : ∀ r : Nat, r ∈ allQuads8 →
      bipartitionFeasible (canonBipart p0) r = bipartitionFeasible p0 r :=
    fun _ hr => canonBipart_feasible_eq hp0_quad hr
  have hpush_feas : ∀ r : Nat, bipartitionFeasible p0 r = bipartitionFeasible q (pullMask L r) := by
    intro r
    unfold bipartitionFeasible
    have ⟨_, _, hint⟩ := interCount8_pushMask r1 r2 q r
    rw [hint, popcount8_pullMask]
  refine ⟨canonBipart p0, hcanon_mem, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with heq | heq | heq
  · rw [heq, hcanon_eq r1 hr1, hpush_feas r1, hp1]; exact hf1
  · rw [heq]
    have hor : bipartitionFeasible (canonBipart p0) (orientRow r1 r2) =
        bipartitionFeasible (canonBipart p0) r2 := by
      unfold orientRow
      by_cases h : 2 ≤ interCount8 r1 r2
      · simp [h]
      · simp [h]
        exact comp_quad_feasible_eq hcanon_pop hr2
    rw [← hor]
    have hor_quad : orientRow r1 r2 ∈ allQuads8 := by
      unfold orientRow
      by_cases h : 2 ≤ interCount8 r1 r2
      · simp [h, hr2]
      · simp [h]
        have hr2_lt : r2 < 256 := List.mem_range.mp (List.mem_filter.mp hr2).1
        have hr2_pop : popcount8 r2 = 4 := of_decide_eq_true (List.mem_filter.mp hr2).2
        have hcomp := popcount8_comp hr2_lt
        apply List.mem_filter.mpr
        refine ⟨List.mem_range.mpr (by omega), ?_⟩
        have h4 : popcount8 (255 - r2) = 4 := by omega
        rw [h4]; rfl
    rw [hcanon_eq _ hor_quad, hpush_feas _]; exact hf2
  · rw [heq, hcanon_eq r3 hr3, hpush_feas r3]; exact hf3

theorem le_three_quads_always_feasible (rows : List Nat)
    (hquads : ∀ r : Nat, r ∈ rows → r ∈ allQuads8) (hlen : rows.length ≤ 3) :
    rowsFeasible8 rows := by
  have h15 : (15 : Nat) ∈ allQuads8 := by decide
  match rows with
  | [] =>
    obtain ⟨p, hp, _⟩ := three_quads_always_feasible 15 15 15 h15 h15 h15
    exact ⟨p, hp, fun _ h => False.elim (List.not_mem_nil h)⟩
  | [r1] =>
    have hr1 := hquads r1 List.mem_cons_self
    obtain ⟨p, hp, hf⟩ := three_quads_always_feasible r1 r1 r1 hr1 hr1 hr1
    exact ⟨p, hp, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [hr]; exact hf r1 List.mem_cons_self⟩
  | [r1, r2] =>
    have hr1 := hquads r1 List.mem_cons_self
    have hr2 := hquads r2 (List.mem_cons_of_mem r1 List.mem_cons_self)
    obtain ⟨p, hp, hf⟩ := three_quads_always_feasible r1 r2 r2 hr1 hr2 hr2
    exact ⟨p, hp, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with heq | heq
      · rw [heq]; exact hf r1 List.mem_cons_self
      · rw [heq]; exact hf r2 (List.mem_cons_of_mem r1 List.mem_cons_self)⟩
  | [r1, r2, r3] =>
    exact three_quads_always_feasible r1 r2 r3
      (hquads r1 List.mem_cons_self)
      (hquads r2 (List.mem_cons_of_mem r1 List.mem_cons_self))
      (hquads r3 (List.mem_cons_of_mem r1 (List.mem_cons_of_mem r2 List.mem_cons_self)))
  | _ :: _ :: _ :: _ :: _ =>
    simp at hlen

/-! ### Exact `R = 4` Sunflower Obstruction (`sunflowerRows8`) -/

theorem sunflowerRows8_length : sunflowerRows8.length = 4 := by decide

theorem sunflowerRows8_all_quads_check :
    sunflowerRows8.all (fun r => decide (r ∈ allQuads8)) = true := by decide

theorem sunflowerRows8_all_quads (r : Nat) (hr : r ∈ sunflowerRows8) : r ∈ allQuads8 :=
  of_decide_eq_true (List.all_eq_true.mp sunflowerRows8_all_quads_check r hr)

theorem sunflowerRows8_kills_all_check :
    allBipartitions8.all (fun p => sunflowerRows8.any (fun r => bipartitionKilled p r)) = true := by
  decide

theorem sunflowerRows8_not_feasible : ¬ rowsFeasible8 sunflowerRows8 := by
  intro ⟨p, hpU, hfeas⟩
  have hany := List.all_eq_true.mp sunflowerRows8_kills_all_check p hpU
  obtain ⟨r, hr, hkill⟩ := List.any_eq_true.mp hany
  have hf := hfeas r hr
  unfold bipartitionKilled at hkill
  rw [hf] at hkill
  exact Bool.noConfusion hkill

/-- Headline Theorem 4: Exact 3-Column Sunflower `2:4` Obstruction Theorem (`R_crit(2, 4) = 4`). -/
theorem sunflower_sparse24_obstruction_exact :
    (allQuads8.length = 70 ∧
     ∀ r : Nat, r ∈ allQuads8 →
       (allBipartitions8.filter (fun p => bipartitionKilled p r)).length = 17) ∧
    (∀ rows : List Nat, (∀ r : Nat, r ∈ rows → r ∈ allQuads8) →
      rows.length ≤ 3 → rowsFeasible8 rows) ∧
    (sunflowerRows8.length = 4 ∧
     (∀ r : Nat, r ∈ sunflowerRows8 → r ∈ allQuads8) ∧
     ¬ rowsFeasible8 sunflowerRows8) :=
  ⟨⟨allQuads8_length, every_quad_kills_seventeen⟩,
   le_three_quads_always_feasible,
   ⟨sunflowerRows8_length, sunflowerRows8_all_quads, sunflowerRows8_not_feasible⟩⟩

end FanoSparse24Perm
