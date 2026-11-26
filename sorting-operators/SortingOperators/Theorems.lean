/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SortingOperators.Defs

/-!
# Cross-Operator Theorems for West Stack-Sorting and Bubble Sort

Proves 7 universal theorems (for arbitrary `List Nat` / `Nodup` lists, zero Mathlib):
1. `inv_bubble_add_des_le_inv`: `invCnt (bubblePass xs) + desCnt xs ≤ invCnt xs`.
2. `des_bubble_le_des`: `desCnt (bubblePass xs) ≤ desCnt xs` (via the stronger carry bound
   `desCnt (bubbleCarry m xs) ≤ desCnt xs`).
3. `westSort_split_max` & `bubblePass_split_max`: exact dual maximum-splitting recurrences
   `S(L ++ [m] ++ R) = S(L) ++ S(R) ++ [m]` and `B(L ++ [m] ++ R) = B(L) ++ R ++ [m]`.
4. `inv_westSort_le_bubble`: `invCnt (westSort xs) ≤ invCnt (bubblePass xs)` for all `Nodup xs`.
5. `des_westSort_le_bubble`: `desCnt (westSort xs) ≤ desCnt (bubblePass xs)` for all `Nodup xs`.
6. `westSort_eq_bubble_of_avoids321`: `Avoids321 xs → westSort xs = bubblePass xs` for all `Nodup xs`,
   paired with `exists_not_avoids321_westSort_eq_bubble` witnessing `xs = [2, 1, 3, 0]`.
7. `inv_bubble_le_pat321_add_pat231`: `invCnt (bubblePass xs) ≤ pat321 xs + pat231 xs` for all `Nodup xs`.
-/

namespace SortingOperators

section BasicListLemmas

theorem countLt_append (x : Nat) : ∀ xs ys : List Nat,
    countLt x (xs ++ ys) = countLt x xs + countLt x ys
  | [], _ => by simp [countLt]
  | a :: xs, ys => by
      simp only [List.cons_append, countLt, countLt_append x xs ys]
      omega

theorem countLt_perm {x : Nat} {xs ys : List Nat} (h : xs.Perm ys) :
    countLt x xs = countLt x ys := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [countLt, ih]
  | swap a b l => simp only [countLt]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Cross-inversions between `xs` and `ys`: pairs `(a ∈ xs, b ∈ ys)` with `a > b`. -/
def crossInv : List Nat → List Nat → Nat
  | [], _ => 0
  | x :: xs, ys => countLt x ys + crossInv xs ys

theorem crossInv_perm_left {xs₁ xs₂ ys : List Nat} (h : xs₁.Perm xs₂) :
    crossInv xs₁ ys = crossInv xs₂ ys := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [crossInv, ih]
  | swap a b l => simp only [crossInv]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem crossInv_perm_right {xs ys₁ ys₂ : List Nat} (h : ys₁.Perm ys₂) :
    crossInv xs ys₁ = crossInv xs ys₂ := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [crossInv, countLt_perm h, ih]

theorem invCnt_append : ∀ xs ys : List Nat,
    invCnt (xs ++ ys) = invCnt xs + invCnt ys + crossInv xs ys
  | [], ys => by simp [invCnt, crossInv]
  | x :: xs, ys => by
      simp only [List.cons_append, invCnt, countLt_append, invCnt_append xs ys, crossInv]
      omega

theorem crossInv_nil_right : ∀ xs : List Nat, crossInv xs [] = 0
  | [] => rfl
  | _ :: xs => by simp [crossInv, countLt, crossInv_nil_right xs]

theorem countLt_singleton_of_le {x m : Nat} (h : x ≤ m) : countLt x [m] = 0 := by
  simp only [countLt]
  have : ¬ m < x := by omega
  simp [this]

theorem crossInv_singleton_max {xs : List Nat} {m : Nat} (h : ∀ a ∈ xs, a ≤ m) :
    crossInv xs [m] = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [crossInv]
      rw [countLt_singleton_of_le (h a (by simp)), ih (fun b hb => h b (by simp [hb]))]

theorem invCnt_append_max {xs : List Nat} {m : Nat} (h : ∀ a ∈ xs, a ≤ m) :
    invCnt (xs ++ [m]) = invCnt xs := by
  rw [invCnt_append, crossInv_singleton_max h]
  simp [invCnt, countLt]

/-- `bubbleCarry m xs` is a permutation of `m :: xs`. -/
theorem bubbleCarry_perm (m : Nat) : ∀ xs : List Nat, (bubbleCarry m xs).Perm (m :: xs)
  | [] => List.Perm.refl _
  | y :: rest => by
      simp only [bubbleCarry]
      split
      · exact (List.Perm.cons y (bubbleCarry_perm m rest)).trans (List.Perm.swap m y rest)
      · exact List.Perm.cons m (bubbleCarry_perm y rest)

/-- `bubblePass xs` is a permutation of `xs`. -/
theorem bubblePass_perm : ∀ xs : List Nat, (bubblePass xs).Perm xs
  | [] => List.Perm.refl _
  | x :: xs => bubbleCarry_perm x xs

/-- `westRun xs stack` is a permutation of `xs ++ stack`. -/
theorem westRun_perm (xs stack : List Nat) : (westRun xs stack).Perm (xs ++ stack) := by
  match xs, stack with
  | [], stack =>
      simp only [westRun, List.nil_append]
      exact List.Perm.refl _
  | x :: xs, [] =>
      simp only [westRun, List.append_nil]
      exact (westRun_perm xs [x]).trans (List.perm_append_singleton x xs)
  | x :: xs, s :: ss =>
      simp only [westRun]
      split
      · have ih := westRun_perm (x :: xs) ss
        have h1 : (s :: westRun (x :: xs) ss).Perm (s :: ((x :: xs) ++ ss)) :=
          List.Perm.cons s ih
        have h2 : (s :: ((x :: xs) ++ ss)).Perm ((x :: xs) ++ s :: ss) :=
          List.perm_middle.symm
        exact h1.trans h2
      · have ih := westRun_perm xs (x :: s :: ss)
        have h2 : (xs ++ x :: s :: ss).Perm ((x :: xs) ++ s :: ss) := by
          exact List.perm_middle
        exact ih.trans h2
termination_by 2 * xs.length + stack.length

/-- `westSort xs` is a permutation of `xs`. -/
theorem westSort_perm (xs : List Nat) : (westSort xs).Perm xs := by
  simpa [westSort] using westRun_perm xs []

end BasicListLemmas

section BubbleInequalities

private theorem desCnt_cons_le_of_lt {y m : Nat} (h : y < m) :
    ∀ rest : List Nat, desCnt (y :: rest) ≤ desCnt (m :: rest)
  | [] => by simp [desCnt]
  | z :: r => by
      simp only [desCnt]
      split <;> split <;> omega

/-- Carry-level inversion-descent inequality:
`invCnt (bubbleCarry m xs) + desCnt (m :: xs) ≤ invCnt (m :: xs)`. -/
theorem inv_bubbleCarry_add_des_le (m : Nat) : ∀ xs : List Nat,
    invCnt (bubbleCarry m xs) + desCnt (m :: xs) ≤ invCnt (m :: xs)
  | [] => by simp [bubbleCarry, invCnt, desCnt]
  | y :: rest => by
      simp only [bubbleCarry]
      split
      · rename_i hmy
        have hperm := bubbleCarry_perm m rest
        have hlt_y : countLt y (bubbleCarry m rest) = countLt y rest := by
          rw [countLt_perm hperm]
          simp only [countLt]
          have : ¬ m < y := by omega
          simp [this]
        have hdes : desCnt (y :: rest) ≤ desCnt (m :: rest) := desCnt_cons_le_of_lt hmy rest
        have hih := inv_bubbleCarry_add_des_le m rest
        simp only [invCnt, countLt, desCnt, hmy, ↓reduceIte] at hih ⊢
        rw [hlt_y]
        omega
      · rename_i hmy
        have hperm := bubbleCarry_perm y rest
        have hlt_m : countLt m (bubbleCarry y rest) = countLt m rest := by
          rw [countLt_perm hperm]
          simp only [countLt]
          have : ¬ y < m := by omega
          simp [this]
        have hih := inv_bubbleCarry_add_des_le y rest
        simp only [invCnt, countLt, desCnt, hmy, ↓reduceIte] at hih ⊢
        rw [hlt_m]
        omega

/-- **Theorem 1 (`inv_bubble_add_des_le_inv`):** For every list `xs : List Nat`,
`invCnt (bubblePass xs) + desCnt xs ≤ invCnt xs`. -/
theorem inv_bubble_add_des_le_inv : ∀ xs : List Nat,
    invCnt (bubblePass xs) + desCnt xs ≤ invCnt xs
  | [] => by simp [bubblePass, invCnt, desCnt]
  | x :: xs => inv_bubbleCarry_add_des_le x xs

/-- First element of `bubbleCarry m xs` (guaranteed nonempty). -/
theorem bubbleCarry_ne_nil (m : Nat) : ∀ xs : List Nat, bubbleCarry m xs ≠ []
  | [] => by simp [bubbleCarry]
  | y :: rest => by
      simp only [bubbleCarry]
      split <;> simp

theorem head_bubbleCarry_eq_min (m y : Nat) (rest : List Nat) :
    (bubbleCarry m (y :: rest)).head (bubbleCarry_ne_nil m (y :: rest)) =
      if m > y then y else m := by
  simp only [bubbleCarry]
  split <;> rfl

theorem desCnt_cons_nonempty (a : Nat) {ys : List Nat} (hne : ys ≠ []) :
    desCnt (a :: ys) = (if a > ys.head hne then 1 else 0) + desCnt ys := by
  cases ys with
  | nil => exact absurd rfl hne
  | cons y r => rfl

/-- Strong carry-level descent bound: `desCnt (bubbleCarry m xs) ≤ desCnt xs` for all `m, xs`. -/
theorem des_bubbleCarry_le_tail (m : Nat) : ∀ xs : List Nat,
    desCnt (bubbleCarry m xs) ≤ desCnt xs
  | [] => by simp [bubbleCarry, desCnt]
  | y :: rest => by
      simp only [bubbleCarry]
      split
      · rename_i hmy
        rw [desCnt_cons_nonempty y (bubbleCarry_ne_nil m rest)]
        have hih := des_bubbleCarry_le_tail m rest
        cases rest with
        | nil =>
            simp [bubbleCarry, desCnt]
            omega
        | cons z r =>
            rw [head_bubbleCarry_eq_min]
            simp only [desCnt]
            by_cases hmz : m > z <;> by_cases hyz : y > z <;> simp [hmz, hyz] <;>
              (try split) <;> omega
      · rename_i hmy
        rw [desCnt_cons_nonempty m (bubbleCarry_ne_nil y rest)]
        have hih := des_bubbleCarry_le_tail y rest
        cases rest with
        | nil =>
            simp [bubbleCarry, desCnt]
            omega
        | cons z r =>
            rw [head_bubbleCarry_eq_min]
            simp only [desCnt]
            by_cases hyz : y > z <;> by_cases hmz : m > z <;> simp [hyz, hmz] <;>
              (try split) <;> omega

/-- **Theorem 2 (`des_bubble_le_des`):** For every list `xs : List Nat`,
`desCnt (bubblePass xs) ≤ desCnt xs`. -/
theorem des_bubble_le_des : ∀ xs : List Nat,
    desCnt (bubblePass xs) ≤ desCnt xs
  | [] => by simp [bubblePass, desCnt]
  | x :: xs => by
      have h1 := des_bubbleCarry_le_tail x xs
      cases xs with
      | nil => simp [bubblePass, bubbleCarry, desCnt]
      | cons y r =>
          simp only [bubblePass, desCnt]
          omega

end BubbleInequalities

section MaxSplitDecomposition

/-- Every element in `xs` has a unique maximum split when `xs` is nonempty and `Nodup`. -/
theorem exists_max_split : ∀ xs : List Nat, xs ≠ [] → xs.Nodup →
    ∃ (L R : List Nat) (m : Nat),
      xs = L ++ m :: R ∧ (∀ a ∈ L, a < m) ∧ (∀ b ∈ R, b < m)
  | [], hne, _ => absurd rfl hne
  | [x], _, _ => ⟨[], [], x, rfl, by simp, by simp⟩
  | x :: y :: rest, _, hnd => by
      have hnd_tail : (y :: rest).Nodup := (List.nodup_cons.mp hnd).2
      have hx_notin : x ∉ y :: rest := (List.nodup_cons.mp hnd).1
      obtain ⟨L, R, m, heq, hL, hR⟩ := exists_max_split (y :: rest) (by simp) hnd_tail
      have hxne : x ≠ m := by
        intro hxm
        apply hx_notin
        rw [heq, hxm]
        simp
      by_cases hgt : m < x
      · refine ⟨[], y :: rest, x, rfl, by simp, ?_⟩
        intro b hb
        rw [heq] at hb
        simp only [List.mem_append, List.mem_cons] at hb
        rcases hb with h | rfl | h
        · exact Nat.lt_trans (hL b h) hgt
        · exact hgt
        · exact Nat.lt_trans (hR b h) hgt
      · have hxm : x < m := by omega
        refine ⟨x :: L, R, m, ?_, ?_, hR⟩
        · simp [heq]
        · intro a ha
          simp only [List.mem_cons] at ha
          rcases ha with rfl | h
          · exact hxm
          · exact hL a h

/-- `bubbleCarry m R = R ++ [m]` when `m` is strictly larger than every element of `R`. -/
theorem bubbleCarry_max (m : Nat) : ∀ R : List Nat, (∀ b ∈ R, b < m) →
    bubbleCarry m R = R ++ [m]
  | [], _ => rfl
  | b :: rest, hR => by
      have hbm : m > b := hR b (by simp)
      simp only [bubbleCarry, hbm, ↓reduceIte, List.cons_append]
      rw [bubbleCarry_max m rest (fun c hc => hR c (by simp [hc]))]

private theorem bubbleCarry_append_max (a m : Nat) (hm : a < m) :
    ∀ (L R : List Nat), (∀ x ∈ L, x < m) → (∀ y ∈ R, y < m) →
      bubbleCarry a (L ++ m :: R) = bubbleCarry a L ++ R ++ [m]
  | [], R, _, hR => by
      have hnot : ¬ a > m := by omega
      simp only [List.nil_append, bubbleCarry, hnot, ↓reduceIte, List.cons_append]
      rw [bubbleCarry_max m R hR]
  | b :: L, R, hL, hR => by
      have hbm : b < m := hL b (by simp)
      have hL' : ∀ x ∈ L, x < m := fun x hx => hL x (by simp [hx])
      simp only [List.cons_append, bubbleCarry]
      split
      · simp only [List.cons_append]
        rw [bubbleCarry_append_max a m hm L R hL' hR]
      · simp only [List.cons_append]
        rw [bubbleCarry_append_max b m hbm L R hL' hR]

/-- **Bubble-sort maximum-splitting theorem:**
If `∀ a ∈ L, a < m` and `∀ b ∈ R, b < m`, then `bubblePass (L ++ m :: R) = bubblePass L ++ R ++ [m]`. -/
theorem bubblePass_split_max (L R : List Nat) (m : Nat)
    (hL : ∀ a ∈ L, a < m) (hR : ∀ b ∈ R, b < m) :
    bubblePass (L ++ m :: R) = bubblePass L ++ R ++ [m] := by
  cases L with
  | nil =>
      simp only [List.nil_append, bubblePass]
      exact bubbleCarry_max m R hR
  | cons a L' =>
      simp only [List.cons_append, bubblePass]
      exact bubbleCarry_append_max a m (hL a (by simp)) L' R (fun x hx => hL x (by simp [hx])) hR

/-- Helper: when `m` exceeds every element in `L` and `stack`, running `westRun` on `L ++ m :: R`
drains `L` and `stack` completely before pushing `m`. -/
private theorem westRun_append_max_left (L R stack : List Nat) (m : Nat)
    (hL : ∀ a ∈ L, a < m) (hs : ∀ s ∈ stack, s < m) :
    westRun (L ++ m :: R) stack = westRun L stack ++ westRun R [m] := by
  match L, stack with
  | [], [] =>
      simp [westRun]
  | [], s :: ss =>
      have hsm : m > s := hs s (by simp)
      simp only [List.nil_append, westRun, hsm, ↓reduceIte, List.cons_append]
      congr 1
      simpa [westRun] using westRun_append_max_left [] R ss m (by simp) (fun t ht => hs t (by simp [ht]))
  | x :: xs, [] =>
      simp only [List.cons_append, westRun]
      exact westRun_append_max_left xs R [x] m
        (fun a ha => hL a (by simp [ha]))
        (fun t ht => by simp only [List.mem_singleton] at ht; subst ht; exact hL t (by simp))
  | x :: xs, s :: ss =>
      simp only [List.cons_append, westRun]
      split
      · simp only [List.cons_append]
        congr 1
        simpa using westRun_append_max_left (x :: xs) R ss m hL (fun t ht => hs t (by simp [ht]))
      · exact westRun_append_max_left xs R (x :: s :: ss) m
          (fun a ha => hL a (by simp [ha]))
          (fun t ht => by
            simp only [List.mem_cons] at ht
            rcases ht with rfl | h
            · exact hL t (by simp)
            · exact hs t (by simp [h]))
termination_by 2 * L.length + stack.length

/-- Helper: when `m` sits at the bottom of the stack and strictly exceeds everything in `R` and
`stack`, `m` stays at the bottom until the very end! -/
private theorem westRun_bottom_max (R stack : List Nat) (m : Nat)
    (hR : ∀ b ∈ R, b < m) (hs : ∀ s ∈ stack, s < m) :
    westRun R (stack ++ [m]) = westRun R stack ++ [m] := by
  match R, stack with
  | [], stack =>
      simp [westRun]
  | x :: xs, [] =>
      have hxm : ¬ x > m := by have := hR x (by simp); omega
      simp only [List.nil_append, westRun, hxm, ↓reduceIte]
      exact westRun_bottom_max xs [x] m
        (fun b hb => hR b (by simp [hb]))
        (fun t ht => by simp only [List.mem_singleton] at ht; subst ht; exact hR t (by simp))
  | x :: xs, s :: ss =>
      simp only [List.cons_append, westRun]
      split
      · simp only [List.cons_append]
        congr 1
        exact westRun_bottom_max (x :: xs) ss m hR (fun t ht => hs t (by simp [ht]))
      · exact westRun_bottom_max xs (x :: s :: ss) m
          (fun b hb => hR b (by simp [hb]))
          (fun t ht => by
            simp only [List.mem_cons] at ht
            rcases ht with rfl | h
            · exact hR t (by simp)
            · exact hs t (by simp [h]))
termination_by 2 * R.length + stack.length

/-- **West stack-sorting maximum-splitting theorem:**
If `∀ a ∈ L, a < m` and `∀ b ∈ R, b < m`, then
`westSort (L ++ m :: R) = westSort L ++ westSort R ++ [m]`. -/
theorem westSort_split_max (L R : List Nat) (m : Nat)
    (hL : ∀ a ∈ L, a < m) (hR : ∀ b ∈ R, b < m) :
    westSort (L ++ m :: R) = westSort L ++ westSort R ++ [m] := by
  unfold westSort
  rw [westRun_append_max_left L R [] m hL (by simp)]
  simp only [List.append_assoc]
  congr 1
  simpa using westRun_bottom_max R [] m hR (by simp)

end MaxSplitDecomposition

section CrossOperatorTheorems

/-- **Theorem 3 (`inv_westSort_le_bubble`):** For every `Nodup` list `xs : List Nat`,
`invCnt (westSort xs) ≤ invCnt (bubblePass xs)`. -/
theorem inv_westSort_le_bubble (xs : List Nat) (hnd : xs.Nodup) :
    invCnt (westSort xs) ≤ invCnt (bubblePass xs) := by
  generalize hn : xs.length = n
  induction n using Nat.strongRecOn generalizing xs with
  | ind n ih =>
    cases xs with
    | nil => simp [westSort, westRun, bubblePass, invCnt]
    | cons x rest =>
      obtain ⟨L, R, m, heq, hL, hR⟩ := exists_max_split (x :: rest) (by simp) hnd
      rw [heq] at hnd hn ⊢
      have hnd_L : L.Nodup := (List.nodup_append.mp hnd).1
      have hnd_R : R.Nodup := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).2
      have hlen_L : L.length < n := by simp [List.length_append] at hn; omega
      have hlen_R : R.length < n := by simp [List.length_append] at hn; omega
      have ihL := ih L.length hlen_L L hnd_L rfl
      have ihR := ih R.length hlen_R R hnd_R rfl
      have hBR : invCnt (bubblePass R) ≤ invCnt R := by
        have := inv_bubble_add_des_le_inv R
        omega
      rw [westSort_split_max L R m hL hR, bubblePass_split_max L R m hL hR]
      have hSL_lt : ∀ a ∈ westSort L ++ westSort R, a ≤ m := by
        intro a ha
        simp only [List.mem_append] at ha
        rcases ha with h | h
        · exact Nat.le_of_lt (hL a ((westSort_perm L).mem_iff.mp h))
        · exact Nat.le_of_lt (hR a ((westSort_perm R).mem_iff.mp h))
      have hBL_lt : ∀ a ∈ bubblePass L ++ R, a ≤ m := by
        intro a ha
        simp only [List.mem_append] at ha
        rcases ha with h | h
        · exact Nat.le_of_lt (hL a ((bubblePass_perm L).mem_iff.mp h))
        · exact Nat.le_of_lt (hR a h)
      rw [invCnt_append_max hSL_lt, invCnt_append_max hBL_lt, invCnt_append, invCnt_append]
      have hcross : crossInv (westSort L) (westSort R) = crossInv (bubblePass L) R := by
        rw [crossInv_perm_left (westSort_perm L), crossInv_perm_right (westSort_perm R),
          ← crossInv_perm_left (bubblePass_perm L)]
      rw [hcross]
      omega

section DesCrossHelpers

private theorem desCnt_append_singleton_max {xs : List Nat} {m : Nat} (h : ∀ a ∈ xs, a ≤ m) :
    desCnt (xs ++ [m]) = desCnt xs := by
  induction xs with
  | nil => simp [desCnt]
  | cons a xs ih =>
      cases xs with
      | nil =>
          have ham : ¬ a > m := by have := h a (by simp); omega
          simp [desCnt, ham]
      | cons b r =>
          simp only [List.cons_append, desCnt]
          have hih := ih (fun c hc => h c (by simp [hc]))
          simp only [List.cons_append] at hih
          rw [hih]

private theorem desCnt_append_split : ∀ (xs ys : List Nat) (hx : xs ≠ []) (hy : ys ≠ []),
    desCnt (xs ++ ys) =
      desCnt xs + desCnt ys + (if xs.getLast hx > ys.head hy then 1 else 0)
  | [], _, hx, _ => absurd rfl hx
  | [a], ys, _, hy => by
      cases ys with
      | nil => exact absurd rfl hy
      | cons b r => simp [desCnt]; omega
  | a :: b :: r, ys, _, hy => by
      simp only [List.cons_append, desCnt]
      have hih := desCnt_append_split (b :: r) ys (by simp) hy
      simp only [List.cons_append] at hih
      rw [hih, List.getLast_cons (by simp : b :: r ≠ [])]
      omega

private theorem westSort_head_of_asc {a b : Nat} (hab : a < b) (rest : List Nat) :
    ∃ tail, westSort (a :: b :: rest) = a :: tail := by
  refine ⟨westRun (b :: rest) [], ?_⟩
  have hgt : b > a := hab
  simp [westSort, westRun, hgt]

private theorem perm_ne_nil {xs ys : List Nat} (hp : xs.Perm ys) (hne : ys ≠ []) : xs ≠ [] := by
  intro h
  subst h
  exact hne hp.nil_eq.symm

private theorem getLast_append_one (xs : List Nat) (m : Nat) :
    (xs ++ [m]).getLast (by simp) = m := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.cons_append]
      rw [List.getLast_cons (by simp)]
      exact ih

private theorem getLast_westSort_eq_bubblePass {xs : List Nat} (hne : xs ≠ []) (hnd : xs.Nodup) :
    (westSort xs).getLast (perm_ne_nil (westSort_perm xs) hne) =
      (bubblePass xs).getLast (perm_ne_nil (bubblePass_perm xs) hne) := by
  obtain ⟨L, R, m, heq, hL, hR⟩ := exists_max_split xs hne hnd
  subst heq
  simp only [westSort_split_max L R m hL hR, bubblePass_split_max L R m hL hR,
    getLast_append_one]

end DesCrossHelpers

/-- **Theorem 4 (`des_westSort_le_bubble`):** For every `Nodup` list `xs : List Nat`,
`desCnt (westSort xs) ≤ desCnt (bubblePass xs)`. -/
theorem des_westSort_le_bubble (xs : List Nat) (hnd : xs.Nodup) :
    desCnt (westSort xs) ≤ desCnt (bubblePass xs) := by
  generalize hn : xs.length = n
  induction n using Nat.strongRecOn generalizing xs with
  | ind n ih =>
    cases xs with
    | nil => simp [westSort, westRun, bubblePass, desCnt]
    | cons x rest =>
      obtain ⟨L, R, m, heq, hL, hR⟩ := exists_max_split (x :: rest) (by simp) hnd
      rw [heq] at hnd hn ⊢
      have hnd_L : L.Nodup := (List.nodup_append.mp hnd).1
      have hnd_R : R.Nodup := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).2
      have hlen_L : L.length < n := by simp [List.length_append] at hn; omega
      have hlen_R : R.length < n := by simp [List.length_append] at hn; omega
      have ihL := ih L.length hlen_L L hnd_L rfl
      have ihR := ih R.length hlen_R R hnd_R rfl
      rw [westSort_split_max L R m hL hR, bubblePass_split_max L R m hL hR]
      have hSL_lt : ∀ a ∈ westSort L ++ westSort R, a ≤ m := by
        intro a ha
        simp only [List.mem_append] at ha
        rcases ha with h | h
        · exact Nat.le_of_lt (hL a ((westSort_perm L).mem_iff.mp h))
        · exact Nat.le_of_lt (hR a ((westSort_perm R).mem_iff.mp h))
      have hBL_lt : ∀ a ∈ bubblePass L ++ R, a ≤ m := by
        intro a ha
        simp only [List.mem_append] at ha
        rcases ha with h | h
        · exact Nat.le_of_lt (hL a ((bubblePass_perm L).mem_iff.mp h))
        · exact Nat.le_of_lt (hR a h)
      rw [desCnt_append_singleton_max hSL_lt, desCnt_append_singleton_max hBL_lt]
      cases L with
      | nil =>
          simp only [westSort, westRun, bubblePass, List.nil_append]
          exact Nat.le_trans ihR (des_bubble_le_des R)
      | cons l ls =>
          cases R with
          | nil =>
              have hS0 : westSort [] = [] := by simp [westSort, westRun]
              rw [hS0, List.append_nil, List.append_nil]
              exact ihL
          | cons r rs =>
              have hSL_ne : westSort (l :: ls) ≠ [] := perm_ne_nil (westSort_perm (l :: ls)) (by simp)
              have hBL_ne : bubblePass (l :: ls) ≠ [] := perm_ne_nil (bubblePass_perm (l :: ls)) (by simp)
              have hSR_ne : westSort (r :: rs) ≠ [] := perm_ne_nil (westSort_perm (r :: rs)) (by simp)
              rw [desCnt_append_split (westSort (l :: ls)) (westSort (r :: rs)) hSL_ne hSR_ne,
                desCnt_append_split (bubblePass (l :: ls)) (r :: rs) hBL_ne (by simp)]
              have hlast : (westSort (l :: ls)).getLast hSL_ne = (bubblePass (l :: ls)).getLast hBL_ne :=
                getLast_westSort_eq_bubblePass (xs := l :: ls) (by simp) hnd_L
              cases rs with
              | nil =>
                  have hSR1 : westSort [r] = [r] := by simp [westSort, westRun]
                  simp only [hSR1, List.head_cons, hlast]
                  have hdes_r : desCnt [r] = 0 := rfl
                  by_cases hb : (bubblePass (l :: ls)).getLast hBL_ne > r <;> simp [hb] <;> omega
              | cons r2 rs' =>
                  have hne_r : r ≠ r2 := by
                    have := (List.nodup_cons.mp hnd_R).1
                    intro heq'; apply this; simp [heq']
                  by_cases hlt : r < r2
                  · obtain ⟨tail, htail⟩ := westSort_head_of_asc hlt rs'
                    have hhead : (westSort (r :: r2 :: rs')).head hSR_ne = r := by
                      simp [htail]
                    have hBR_le : desCnt (bubblePass (r :: r2 :: rs')) ≤ desCnt (r :: r2 :: rs') :=
                      des_bubble_le_des (r :: r2 :: rs')
                    rw [hlast, hhead]
                    simp only [List.head_cons]
                    by_cases hb : (bubblePass (l :: ls)).getLast hBL_ne > r <;> simp [hb] <;> omega
                  · have hgt : r > r2 := by omega
                    have hBR_strict : desCnt (bubblePass (r :: r2 :: rs')) + 1 ≤
                        desCnt (r :: r2 :: rs') := by
                      have h1 := des_bubbleCarry_le_tail r (r2 :: rs')
                      simp only [bubblePass, desCnt, hgt, ↓reduceIte] at h1 ⊢
                      omega
                    have h01 : (if (westSort (l :: ls)).getLast hSL_ne >
                        (westSort (r :: r2 :: rs')).head hSR_ne then 1 else 0) ≤ 1 := by
                      split <;> omega
                    omega

section PatternTheorems

private theorem countLt_pos_of_mem_lt {x y : Nat} {ys : List Nat} (hy : y ∈ ys) (h : y < x) :
    0 < countLt x ys := by
  induction ys with
  | nil => simp at hy
  | cons z zs ih =>
      simp only [List.mem_cons] at hy
      simp only [countLt]
      rcases hy with rfl | hmem
      · simp [h]; omega
      · have := ih hmem; omega

private theorem westRun_eq_append_of_sorted (xs stack : List Nat)
    (hnd : xs.Nodup) (hinv : invCnt xs = 0)
    (hord : ∀ s ∈ stack, ∀ x ∈ xs, s < x) :
    westRun xs stack = stack ++ xs := by
  match xs, stack with
  | [], stack =>
      simp [westRun]
  | x :: xs, [] =>
      simp only [westRun, List.nil_append]
      have hnd_xs : xs.Nodup := (List.nodup_cons.mp hnd).2
      have hx_notin : x ∉ xs := (List.nodup_cons.mp hnd).1
      have hinv_xs : invCnt xs = 0 := by simp only [invCnt] at hinv; omega
      have hlt0 : countLt x xs = 0 := by simp only [invCnt] at hinv; omega
      have hx_lt : ∀ y ∈ xs, x < y := by
        intro y hy
        have hne : x ≠ y := fun h => hx_notin (h ▸ hy)
        have hnotlt : ¬ y < x := fun h => by
          have := countLt_pos_of_mem_lt hy h
          omega
        omega
      have hrec := westRun_eq_append_of_sorted xs [x] hnd_xs hinv_xs (by
        intro s hs y hy
        simp only [List.mem_singleton] at hs
        subst hs
        exact hx_lt y hy)
      simpa using hrec
  | x :: xs, s :: ss =>
      have hgt : x > s := hord s (by simp) x (by simp)
      simp only [westRun, hgt, ↓reduceIte, List.cons_append]
      congr 1
      exact westRun_eq_append_of_sorted (x :: xs) ss hnd hinv
        (fun t ht y hy => hord t (by simp [ht]) y hy)
termination_by 2 * xs.length + stack.length

theorem westSort_eq_self_of_inv_zero {xs : List Nat} (hnd : xs.Nodup) (hinv : invCnt xs = 0) :
    westSort xs = xs := by
  simpa [westSort] using westRun_eq_append_of_sorted xs [] hnd hinv (by simp)

private theorem countPairs321_append (x : Nat) : ∀ xs ys : List Nat,
    countPairs321 x xs ≤ countPairs321 x (xs ++ ys)
  | [], _ => Nat.zero_le _
  | y :: xs, ys => by
      simp only [List.cons_append, countPairs321, countLt_append]
      have hih := countPairs321_append x xs ys
      split <;> omega

private theorem pat321_append_ge : ∀ xs ys : List Nat,
    pat321 xs + pat321 ys ≤ pat321 (xs ++ ys)
  | [], ys => by simp [pat321]
  | x :: xs, ys => by
      simp only [List.cons_append, pat321]
      have h1 := countPairs321_append x xs ys
      have h2 := pat321_append_ge xs ys
      omega

private theorem countPairs321_max (m : Nat) : ∀ R : List Nat, (∀ b ∈ R, b < m) →
    countPairs321 m R = invCnt R
  | [], _ => rfl
  | b :: rest, hR => by
      have hbm : m > b := hR b (by simp)
      simp only [countPairs321, invCnt, hbm, ↓reduceIte]
      rw [countPairs321_max m rest (fun c hc => hR c (by simp [hc]))]

theorem pat321_split_max_ge (L R : List Nat) (m : Nat) (hR : ∀ b ∈ R, b < m) :
    pat321 L + invCnt R ≤ pat321 (L ++ m :: R) := by
  have h1 := pat321_append_ge L (m :: R)
  simp only [pat321, countPairs321_max m R hR] at h1
  omega

/-- **Theorem 5 (`westSort_eq_bubble_of_avoids321`):** On every `321`-avoiding `Nodup` list `xs`,
West's stack-sorting operator coincides identically with a single bubble-sort pass:
`westSort xs = bubblePass xs`. -/
theorem westSort_eq_bubble_of_avoids321 (xs : List Nat) (hnd : xs.Nodup) (hav : Avoids321 xs) :
    westSort xs = bubblePass xs := by
  generalize hn : xs.length = n
  induction n using Nat.strongRecOn generalizing xs with
  | ind n ih =>
    cases xs with
    | nil => simp [westSort, westRun, bubblePass]
    | cons x rest =>
      obtain ⟨L, R, m, heq, hL, hR⟩ := exists_max_split (x :: rest) (by simp) hnd
      rw [heq] at hnd hn hav ⊢
      have hnd_L : L.Nodup := (List.nodup_append.mp hnd).1
      have hnd_R : R.Nodup := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).2
      have hlen_L : L.length < n := by simp [List.length_append] at hn; omega
      have hpat := pat321_split_max_ge L R m hR
      unfold Avoids321 at hav
      have hav_L : Avoids321 L := by unfold Avoids321; omega
      have hinv_R : invCnt R = 0 := by omega
      rw [westSort_split_max L R m hL hR, bubblePass_split_max L R m hL hR,
        ih L.length hlen_L L hnd_L hav_L rfl, westSort_eq_self_of_inv_zero hnd_R hinv_R]

/-- **Theorem 6 (`exists_not_avoids321_westSort_eq_bubble`):** The `321`-avoidance sufficiency
condition is strict: `xs = [2, 1, 3, 0]` is a `Nodup` list containing a `321` pattern (`(2, 1, 0)`)
on which `westSort xs = bubblePass xs` nevertheless holds. -/
theorem exists_not_avoids321_westSort_eq_bubble :
    ∃ xs : List Nat, xs.Nodup ∧ ¬ Avoids321 xs ∧ westSort xs = bubblePass xs := by
  refine ⟨[2, 1, 3, 0], by decide, ?_, by simp [westSort, westRun, bubblePass, bubbleCarry]⟩
  unfold Avoids321
  decide

private theorem countPairs231_append_max (a m : Nat) (ham : a < m) :
    ∀ L R : List Nat,
      countPairs231 a L + countLt a R ≤ countPairs231 a (L ++ m :: R)
  | [], R => by
      have hma : m > a := ham
      simp only [List.nil_append, countPairs231, hma, ↓reduceIte]
      omega
  | y :: L, R => by
      simp only [List.cons_append, countPairs231, countLt_append]
      have hih := countPairs231_append_max a m ham L R
      split <;> omega

theorem pat231_split_max_ge : ∀ (L R : List Nat) (m : Nat), (∀ a ∈ L, a < m) →
    pat231 L + crossInv L R ≤ pat231 (L ++ m :: R)
  | [], _, _, _ => by simp [pat231, crossInv]
  | a :: L, R, m, hL => by
      have ham : a < m := hL a (by simp)
      have h1 := countPairs231_append_max a m ham L R
      have h2 := pat231_split_max_ge L R m (fun x hx => hL x (by simp [hx]))
      simp only [List.cons_append, pat231, crossInv]
      omega

/-- **Theorem 7 (`inv_bubble_le_pat321_add_pat231`):** For every `Nodup` list `xs : List Nat`,
the inversions remaining after one bubble-sort pass are bounded by the total number of `321` and
`231` patterns in `xs`: `invCnt (bubblePass xs) ≤ pat321 xs + pat231 xs`. -/
theorem inv_bubble_le_pat321_add_pat231 (xs : List Nat) (hnd : xs.Nodup) :
    invCnt (bubblePass xs) ≤ pat321 xs + pat231 xs := by
  generalize hn : xs.length = n
  induction n using Nat.strongRecOn generalizing xs with
  | ind n ih =>
    cases xs with
    | nil => simp [bubblePass, invCnt, pat321, pat231]
    | cons x rest =>
      obtain ⟨L, R, m, heq, hL, hR⟩ := exists_max_split (x :: rest) (by simp) hnd
      rw [heq] at hnd hn ⊢
      have hnd_L : L.Nodup := (List.nodup_append.mp hnd).1
      have hlen_L : L.length < n := by simp [List.length_append] at hn; omega
      have ihL := ih L.length hlen_L L hnd_L rfl
      rw [bubblePass_split_max L R m hL hR]
      have hBL_lt : ∀ a ∈ bubblePass L ++ R, a ≤ m := by
        intro a ha
        simp only [List.mem_append] at ha
        rcases ha with h | h
        · exact Nat.le_of_lt (hL a ((bubblePass_perm L).mem_iff.mp h))
        · exact Nat.le_of_lt (hR a h)
      rw [invCnt_append_max hBL_lt, invCnt_append, crossInv_perm_left (bubblePass_perm L)]
      have h321 := pat321_split_max_ge L R m hR
      have h231 := pat231_split_max_ge L R m hL
      omega

end PatternTheorems

end CrossOperatorTheorems

end SortingOperators
