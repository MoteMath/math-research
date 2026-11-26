/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakBruhatCommutators.Bubble

/-!
# Exact Set-Theoretic Theory of West Stack-Sorting and Pop-Stack Sorting

Proves the complete Weak-Bruhat inversion-set characterizations and right-valley lemmas for:
- West's stack-sorting operator `westSort` (`S`):
  - `westSort_perm`: `(westSort xs).Perm xs`
  - `westSort_split_max`: `westSort (l ++ m :: r) = westSort l ++ westSort r ++ [m]`
  - `invSet_westSort_iff`: `IsInv (westSort xs) a b ↔ IsInv xs a b ∧ ∃ c, a < c ∧ Before xs a c ∧ Before xs c b`
  - `rightValley_of_isDesBot_westSort` and `inv_rightValley_westSort`
- Pop-stack sorting operator `popSort` (`P`):
  - `popSort_perm`: `(popSort xs).Perm xs`
  - `invSet_popSort_iff`: `IsInv (popSort xs) a b ↔ IsInv xs a b ∧ HasAscentBetween xs a b`
  - `rightValley_of_isDesBot_popSort` and `inv_rightValley_popSort`
-/

namespace WeakBruhatCommutators

section StrictDecHelpers

/-- A list is strictly decreasing if every adjacent pair satisfies `x > y`. -/
def StrictlyDec : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => y < x ∧ StrictlyDec (y :: rest)

theorem strictlyDec_no_adj_ascent : ∀ {l : List Nat}, StrictlyDec l →
    ∀ {u v : Nat}, Adj l u v → ¬ (u < v)
  | [], _, _, _, ⟨l₁, _, h⟩ => by cases l₁ <;> simp at h
  | [_], _, _, _, ⟨l₁, _, h⟩ => by cases l₁ <;> simp at h
  | x :: y :: rest, ⟨hxy, hrest⟩, u, v, ⟨l₁, l₂, heq⟩ => by
      cases l₁ with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at heq
          rcases heq with ⟨rfl, rfl, _⟩
          omega
      | cons z l₁' =>
          simp only [List.cons_append, List.cons.injEq] at heq
          exact strictlyDec_no_adj_ascent hrest ⟨l₁', l₂, heq.2⟩

theorem strictlyDec_of_no_adj_ascent : ∀ {l : List Nat}, l.Nodup →
    (∀ u v, Adj l u v → ¬ (u < v)) → StrictlyDec l
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | x :: y :: rest, hnd, hno => by
      have hne : x ≠ y := by
        intro h; subst h
        exact (List.nodup_cons.mp hnd).1 (by simp)
      have hnotlt : ¬ (x < y) := hno x y ⟨[], rest, by simp⟩
      refine ⟨by omega, strictlyDec_of_no_adj_ascent (List.nodup_cons.mp hnd).2 ?_⟩
      intro u v ⟨l₁, l₂, heq⟩
      exact hno u v ⟨x :: l₁, l₂, by simp [heq]⟩

theorem strictlyDec_before_gt : ∀ {l : List Nat}, StrictlyDec l →
    ∀ {a b : Nat}, Before l a b → b < a
  | [], _, _, _, ⟨l₁, _, _, h⟩ => by cases l₁ <;> simp at h
  | [_], _, _, _, ⟨l₁, l₂, _, h⟩ => by cases l₁ <;> simp at h
  | x :: y :: rest, ⟨hxy, hrest⟩, a, b, ⟨l₁, l₂, l₃, heq⟩ => by
      cases l₁ with
      | nil =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
          rcases heq with ⟨rfl, htail⟩
          cases l₂ with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at htail
              rcases htail with ⟨rfl, _⟩
              exact hxy
          | cons z l₂' =>
              simp only [List.cons_append, List.cons.injEq] at htail
              rcases htail with ⟨rfl, htail2⟩
              have hyb : b < y := strictlyDec_before_gt hrest ⟨[], l₂', l₃, by simp [htail2]⟩
              omega
      | cons z l₁' =>
          simp only [List.cons_append, List.cons.injEq] at heq
          exact strictlyDec_before_gt hrest ⟨l₁', l₂, l₃, heq.2⟩

theorem strictlyDec_append_left {l₁ l₂ : List Nat} (h : StrictlyDec (l₁ ++ l₂)) :
    StrictlyDec l₁ := by
  induction l₁ with
  | nil => trivial
  | cons x rest ih =>
      cases rest with
      | nil => trivial
      | cons y rest' =>
          simp only [List.cons_append, StrictlyDec] at h
          exact ⟨h.1, ih h.2⟩

theorem strictlyDec_append_right {l₁ l₂ : List Nat} (h : StrictlyDec (l₁ ++ l₂)) :
    StrictlyDec l₂ := by
  induction l₁ with
  | nil => exact h
  | cons x rest ih =>
      cases rest with
      | nil =>
          cases l₂ with
          | nil => trivial
          | cons y l₂' => exact h.2
      | cons y rest' =>
          exact ih h.2

/-- If `a < b` and `Before xs a b`, there is an adjacent ascent in the segment from `a` to `b`. -/
theorem hasAscentBetween_of_lt {xs : List Nat} (hnd : xs.Nodup) {a b : Nat}
    (hlt : a < b) (hbef : Before xs a b) : HasAscentBetween xs a b := by
  rcases hbef with ⟨l₁, l₂, l₃, rfl⟩
  have hnd_seg : (a :: l₂ ++ [b]).Nodup := by
    have h1 : (a :: l₂ ++ b :: l₃).Nodup :=
      (List.nodup_append.mp (by simpa [List.append_assoc] using hnd)).2.1
    have h2 : ((a :: l₂ ++ [b]) ++ l₃).Nodup := by simpa [List.append_assoc] using h1
    exact (List.nodup_append.mp h2).1
  by_cases hdec : StrictlyDec (a :: l₂ ++ [b])
  · exfalso
    have hba : b < a := strictlyDec_before_gt hdec ⟨[], l₂, [], by simp⟩
    omega
  · -- Not strictly decreasing on a Nodup list implies some adjacent ascent exists!
    suffices hex : ∀ (l : List Nat), l.Nodup → ¬ StrictlyDec l → ∃ u v, u < v ∧ Adj l u v by
      obtain ⟨u, v, huv, hadj⟩ := hex (a :: l₂ ++ [b]) hnd_seg hdec
      exact ⟨l₁, l₂, l₃, u, v, rfl, huv, hadj⟩
    intro l
    induction l with
    | nil => intro _ h; exact absurd trivial h
    | cons x rest ih =>
        cases rest with
        | nil => intro _ h; exact absurd trivial h
        | cons y r =>
            intro hndl hnot
            have hne : x ≠ y := fun heq => (List.nodup_cons.mp hndl).1 (by simp [heq])
            by_cases hxy : x < y
            · exact ⟨x, y, hxy, [], r, by simp⟩
            · have hyx : y < x := by omega
              have hnot' : ¬ StrictlyDec (y :: r) := fun hr => hnot ⟨hyx, hr⟩
              obtain ⟨u, v, huv, p₁, p₂, hp⟩ := ih (List.nodup_cons.mp hndl).2 hnot'
              exact ⟨u, v, huv, x :: p₁, p₂, by simp [hp]⟩

/-- On a `Nodup` list, `HasAscentBetween xs a b` is equivalent to `Before xs a b` and the contiguous
segment from `a` to `b` not being `StrictlyDec`. -/
theorem hasAscentBetween_iff_not_strictlyDec {l₁ l₂ l₃ : List Nat} {a b : Nat}
    (hnd : (l₁ ++ a :: l₂ ++ b :: l₃).Nodup) :
    HasAscentBetween (l₁ ++ a :: l₂ ++ b :: l₃) a b ↔ ¬ StrictlyDec (a :: l₂ ++ [b]) := by
  constructor
  · rintro ⟨p₁, p₂, p₃, u, v, heq, huv, hadj⟩
    have hnd1 : (l₁ ++ a :: (l₂ ++ b :: l₃)).Nodup := by simpa [List.append_assoc] using hnd
    have heq1 : l₁ ++ a :: (l₂ ++ b :: l₃) = p₁ ++ a :: (p₂ ++ b :: p₃) := by
      simpa [List.append_assoc] using heq
    obtain ⟨_, hr1⟩ := append_cons_eq_unique hnd1 heq1
    have hnd2 : (l₂ ++ b :: l₃).Nodup := (List.nodup_cons.mp (List.nodup_append.mp hnd1).2.1).2
    obtain ⟨hl2, _⟩ := append_cons_eq_unique hnd2 hr1
    subst hl2
    intro hdec
    exact strictlyDec_no_adj_ascent hdec hadj huv
  · intro hnot
    have hnd_seg : (a :: l₂ ++ [b]).Nodup := by
      have h1 : (a :: l₂ ++ b :: l₃).Nodup :=
        (List.nodup_append.mp (by simpa [List.append_assoc] using hnd)).2.1
      have h2 : ((a :: l₂ ++ [b]) ++ l₃).Nodup := by simpa [List.append_assoc] using h1
      exact (List.nodup_append.mp h2).1
    suffices hex : ∀ (l : List Nat), l.Nodup → ¬ StrictlyDec l → ∃ u v, u < v ∧ Adj l u v by
      obtain ⟨u, v, huv, hadj⟩ := hex (a :: l₂ ++ [b]) hnd_seg hnot
      exact ⟨l₁, l₂, l₃, u, v, rfl, huv, hadj⟩
    intro l
    induction l with
    | nil => intro _ h; exact absurd trivial h
    | cons x rest ih =>
        cases rest with
        | nil => intro _ h; exact absurd trivial h
        | cons y r =>
            intro hndl hnotl
            have hne : x ≠ y := fun heq => (List.nodup_cons.mp hndl).1 (by simp [heq])
            by_cases hxy : x < y
            · exact ⟨x, y, hxy, [], r, by simp⟩
            · have hyx : y < x := by omega
              have hnot' : ¬ StrictlyDec (y :: r) := fun hr => hnotl ⟨hyx, hr⟩
              obtain ⟨u, v, huv, p₁, p₂, hp⟩ := ih (List.nodup_cons.mp hndl).2 hnot'
              exact ⟨u, v, huv, x :: p₁, p₂, by simp [hp]⟩

/-- Extending a segment to the left preserves `HasAscentBetween`. -/
theorem hasAscentBetween_extend_left {xs : List Nat} (hnd : xs.Nodup) {x a b : Nat}
    (hxa : Before xs x a) (hab : HasAscentBetween xs a b) : HasAscentBetween xs x b := by
  rcases hxa with ⟨p₁, p₂, p₃, rfl⟩
  rcases hab with ⟨l₁, l₂, l₃, u, v, heq, huv, q₁, q₂, hq⟩
  have h1 : (p₁ ++ x :: p₂) ++ a :: p₃ = l₁ ++ a :: (l₂ ++ b :: l₃) := by
    simpa [List.append_assoc] using heq
  have hnd1 : ((p₁ ++ x :: p₂) ++ a :: p₃).Nodup := by simpa [List.append_assoc] using hnd
  obtain ⟨_, hr⟩ := append_cons_eq_unique hnd1 h1
  refine ⟨p₁, p₂ ++ a :: l₂, l₃, u, v, ?_, huv, x :: p₂ ++ q₁, q₂, ?_⟩
  · rw [hr]; simp [List.append_assoc]
  · have hq' : a :: l₂ ++ [b] = q₁ ++ u :: v :: q₂ := hq
    calc x :: (p₂ ++ a :: l₂) ++ [b]
        = x :: p₂ ++ (a :: l₂ ++ [b]) := by simp [List.append_assoc]
      _ = x :: p₂ ++ (q₁ ++ u :: v :: q₂) := by rw [hq']
      _ = (x :: p₂ ++ q₁) ++ u :: v :: q₂ := by simp [List.append_assoc]

/-- Extending a segment to the right preserves `HasAscentBetween`. -/
theorem hasAscentBetween_extend_right {xs : List Nat} (hnd : xs.Nodup) {a b y : Nat}
    (hab : HasAscentBetween xs a b) (hby : Before xs b y) : HasAscentBetween xs a y := by
  rcases hab with ⟨l₁, l₂, l₃, u, v, rfl, huv, q₁, q₂, hq⟩
  rcases hby with ⟨p₁, p₂, p₃, heq⟩
  have h1 : (l₁ ++ a :: l₂) ++ b :: l₃ = p₁ ++ b :: (p₂ ++ y :: p₃) := by
    simpa [List.append_assoc] using heq
  have hnd1 : ((l₁ ++ a :: l₂) ++ b :: l₃).Nodup := by simpa [List.append_assoc] using hnd
  obtain ⟨_, hr⟩ := append_cons_eq_unique hnd1 h1
  refine ⟨l₁, l₂ ++ b :: p₂, p₃, u, v, ?_, huv, q₁, q₂ ++ p₂ ++ [y], ?_⟩
  · rw [hr]; simp [List.append_assoc]
  · calc a :: (l₂ ++ b :: p₂) ++ [y]
        = (a :: l₂ ++ [b]) ++ p₂ ++ [y] := by simp [List.append_assoc]
      _ = (q₁ ++ u :: v :: q₂) ++ p₂ ++ [y] := by rw [hq]
      _ = q₁ ++ u :: v :: (q₂ ++ p₂ ++ [y]) := by simp [List.append_assoc]

end StrictDecHelpers

section WestTheory

theorem westRun_perm (xs stack : List Nat) : (westRun xs stack).Perm (xs ++ stack) := by
  match xs, stack with
  | [], stack => simp [westRun]
  | x :: xs, [] =>
      simp only [westRun]
      exact (westRun_perm xs [x]).trans (by simp [List.perm_append_singleton])
  | x :: xs, s :: ss =>
      simp only [westRun]
      split
      · have ih := westRun_perm (x :: xs) ss
        exact (List.Perm.cons s ih).trans (by
          have h1 : (s :: ((x :: xs) ++ ss)).Perm ((x :: xs) ++ s :: ss) := by
            simpa [List.append_assoc] using (List.perm_middle (l₁ := x :: xs) (l₂ := ss) (a := s)).symm
          exact h1)
      · have ih := westRun_perm xs (x :: s :: ss)
        exact ih.trans (by
          simp only [List.cons_append]
          exact List.perm_middle (l₁ := xs) (l₂ := s :: ss) (a := x))
termination_by 2 * xs.length + stack.length

theorem westSort_perm (xs : List Nat) : (westSort xs).Perm xs := by
  have h := westRun_perm xs []
  simp only [List.append_nil] at h
  exact h

/-- Splitting `westRun` when encountering a strict maximum `m` exceeding all elements of `l` and `stack`. -/
theorem westRun_append_max (l r stack : List Nat) (m : Nat)
    (hl : ∀ x ∈ l, x < m) (hs : ∀ s ∈ stack, s < m) :
    westRun (l ++ m :: r) stack = westRun l stack ++ westRun r [m] := by
  match l, stack with
  | [], [] => simp [westRun]
  | [], s :: ss =>
      have hms : m > s := hs s (by simp)
      simp only [List.nil_append, westRun, hms, ↓reduceIte]
      have ih := westRun_append_max [] r ss m hl (fun t ht => hs t (by simp [ht]))
      simpa [westRun] using congrArg (s :: ·) ih
  | x :: l', [] =>
      simp only [List.cons_append, westRun]
      exact westRun_append_max l' r [x] m
        (fun y hy => hl y (by simp [hy]))
        (fun t ht => by simp only [List.mem_singleton] at ht; rw [ht]; exact hl x (by simp))
  | x :: l', s :: ss =>
      simp only [List.cons_append, westRun]
      by_cases hxs : x > s
      · simp only [hxs, ↓reduceIte]
        have ih := westRun_append_max (x :: l') r ss m hl (fun t ht => hs t (by simp [ht]))
        simpa using congrArg (s :: ·) ih
      · simp only [hxs, ↓reduceIte]
        exact westRun_append_max l' r (x :: s :: ss) m
          (fun y hy => hl y (by simp [hy]))
          (fun t ht => by
            rw [List.mem_cons] at ht
            rcases ht with htx | ht'
            · rw [htx]; exact hl x (by simp)
            · exact hs t ht')
termination_by 2 * l.length + stack.length

/-- A bottom-of-stack strict maximum `m` is emitted at the very end of `westRun`. -/
theorem westRun_append_bottom (r stack : List Nat) (m : Nat)
    (hr : ∀ x ∈ r, x < m) (hs : ∀ s ∈ stack, s < m) :
    westRun r (stack ++ [m]) = westRun r stack ++ [m] := by
  match r, stack with
  | [], stack => simp [westRun]
  | x :: r', [] =>
      have hxm : ¬ (x > m) := by have := hr x (by simp); omega
      simp only [List.nil_append, westRun, hxm, ↓reduceIte]
      have ih := westRun_append_bottom r' [x] m
        (fun y hy => hr y (by simp [hy]))
        (fun t ht => by simp only [List.mem_singleton] at ht; rw [ht]; exact hr x (by simp))
      simpa using ih
  | x :: r', s :: ss =>
      simp only [List.cons_append, westRun]
      by_cases hxs : x > s
      · simp only [hxs, ↓reduceIte]
        have ih := westRun_append_bottom (x :: r') ss m hr (fun t ht => hs t (by simp [ht]))
        simpa using congrArg (s :: ·) ih
      · simp only [hxs, ↓reduceIte]
        have ih := westRun_append_bottom r' (x :: s :: ss) m
          (fun y hy => hr y (by simp [hy]))
          (fun t ht => by
            rw [List.mem_cons] at ht
            rcases ht with htx | ht'
            · rw [htx]; exact hr x (by simp)
            · exact hs t ht')
        simpa using ih
termination_by 2 * r.length + stack.length

/-- **Maximum-splitting identity for West's stack-sorting operator:**
If `m` exceeds every element of `l` and `r`, then `westSort (l ++ m :: r) = westSort l ++ westSort r ++ [m]`. -/
theorem westSort_split_max (l r : List Nat) (m : Nat)
    (hl : ∀ x ∈ l, x < m) (hr : ∀ y ∈ r, y < m) :
    westSort (l ++ m :: r) = westSort l ++ westSort r ++ [m] := by
  unfold westSort
  rw [westRun_append_max l r [] m hl (by simp)]
  have hb := westRun_append_bottom r [] m hr (by simp)
  simpa [List.append_assoc] using congrArg (westRun l [] ++ ·) hb

/-- Every nonempty `Nodup` list splits uniquely at its maximum element. -/
theorem exists_split_max : ∀ {xs : List Nat}, xs ≠ [] → xs.Nodup →
    ∃ l m r, xs = l ++ m :: r ∧ (∀ x ∈ l, x < m) ∧ (∀ y ∈ r, y < m)
  | [], hne, _ => absurd rfl hne
  | [x], _, _ => ⟨[], x, [], by simp, by simp, by simp⟩
  | x :: y :: rest, _, hnd => by
      have hnd' : (y :: rest).Nodup := (List.nodup_cons.mp hnd).2
      have hx_notin : x ∉ y :: rest := (List.nodup_cons.mp hnd).1
      obtain ⟨l, m, r, heq, hl, hr⟩ := exists_split_max (by simp : y :: rest ≠ []) hnd'
      have hxm_ne : x ≠ m := fun h => hx_notin (by rw [h, heq]; simp)
      by_cases hxm : m < x
      · refine ⟨[], x, y :: rest, by simp, by simp, ?_⟩
        intro z hz
        rw [heq] at hz
        simp only [List.mem_append, List.mem_cons] at hz
        rcases hz with hzl | rfl | hzr
        · exact Nat.lt_trans (hl z hzl) hxm
        · exact hxm
        · exact Nat.lt_trans (hr z hzr) hxm
      · have hlt : x < m := by omega
        refine ⟨x :: l, m, r, by simp [heq], ?_, hr⟩
        intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hzl
        · exact hlt
        · exact hl z hzl

/-- **Exact inversion-set characterization of West's stack-sorting operator (`S`):**
For any `Nodup` list `xs`, `(a, b) ∈ InvSet(westSort xs)` if and only if `(a, b) ∈ InvSet(xs)`
and there exists `c > a` lying strictly between `a` and `b` in `xs`. -/
theorem invSet_westSort_iff : ∀ {xs : List Nat}, xs.Nodup → ∀ (a b : Nat),
    IsInv (westSort xs) a b ↔ IsInv xs a b ∧ ∃ c, a < c ∧ Before xs a c ∧ Before xs c b := by
  intro xs
  suffices hstrong : ∀ n : Nat, ∀ xs : List Nat, xs.length ≤ n → xs.Nodup → ∀ a b : Nat,
      IsInv (westSort xs) a b ↔ IsInv xs a b ∧ ∃ c, a < c ∧ Before xs a c ∧ Before xs c b by
    exact hstrong xs.length xs (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
      intro xs hlen _ a b
      cases xs with
      | nil => simp [westSort, westRun, IsInv, Before]
      | cons _ _ => simp at hlen
  | succ n ih =>
      intro xs hlen hnd a b
      cases xs with
      | nil => simp [westSort, westRun, IsInv, Before]
      | cons x rest =>
          obtain ⟨l, m, r, heq, hl, hr⟩ := exists_split_max (by simp : x :: rest ≠ []) hnd
          rw [heq] at hlen hnd ⊢
          have hlen_l : l.length ≤ n := by simp at hlen; omega
          have hlen_r : r.length ≤ n := by simp at hlen; omega
          have hnd_l : l.Nodup := (List.nodup_append.mp hnd).1
          have hnd_mr : (m :: r).Nodup := (List.nodup_append.mp hnd).2.1
          have hnd_r : r.Nodup := (List.nodup_cons.mp hnd_mr).2
          have hsplit := westSort_split_max l r m hl hr
          have hnd_S : (westSort (l ++ m :: r)).Nodup :=
            ((westSort_perm _).nodup_iff).mpr hnd
          rw [hsplit] at hnd_S ⊢
          have hnd_SlSr : (westSort l ++ westSort r).Nodup :=
            (List.nodup_append.mp hnd_S).1
          -- Neither `a` nor `b` can be `m` on either side:
          have hmax_all : ∀ z ∈ l ++ m :: r, z ≤ m := by
            intro z hz
            simp only [List.mem_append, List.mem_cons] at hz
            rcases hz with hzl | hzm | hzr
            · exact Nat.le_of_lt (hl z hzl)
            · rw [hzm]; exact Nat.le_refl m
            · exact Nat.le_of_lt (hr z hzr)
          constructor
          · intro ⟨hba, hbef⟩
            have ha_mem : a ∈ (westSort l ++ westSort r) ++ [m] := mem_of_before_left hbef
            have hb_mem : b ∈ (westSort l ++ westSort r) ++ [m] := mem_of_before_right hbef
            have hb_lt_m : b < m := by
              have ha_in_orig : a ∈ l ++ m :: r := by
                rw [← (westSort_perm (l ++ m :: r)).mem_iff, hsplit]; exact ha_mem
              have := hmax_all a ha_in_orig; omega
            have hbef_lr : Before (westSort l ++ westSort r) a b := by
              rcases before_append_cases hnd_S hbef with h1 | h2 | ⟨_, hb_m⟩
              · exact h1
              · exfalso; rcases h2 with ⟨p₁, p₂, p₃, h⟩; cases p₁ <;> simp at h
              · simp only [List.mem_singleton] at hb_m; omega
            rcases before_append_cases hnd_SlSr hbef_lr with hll | hrr | ⟨hal, hbr⟩
            · have hih := (ih l hlen_l hnd_l a b).mp ⟨hba, hll⟩
              rcases hih with ⟨⟨_, hab_l⟩, c, hac, hac_l, hcb_l⟩
              exact ⟨⟨hba, before_append_left hab_l⟩, c, hac,
                before_append_left hac_l, before_append_left hcb_l⟩
            · have hih := (ih r hlen_r hnd_r a b).mp ⟨hba, hrr⟩
              rcases hih with ⟨⟨_, hab_r⟩, c, hac, hac_r, hcb_r⟩
              exact ⟨⟨hba, before_append_right (before_append_right (l₁ := [m]) hab_r)⟩,
                c, hac,
                before_append_right (before_append_right (l₁ := [m]) hac_r),
                before_append_right (before_append_right (l₁ := [m]) hcb_r)⟩
            · have ha_l : a ∈ l := (westSort_perm l).mem_iff.mp hal
              have hb_r : b ∈ r := (westSort_perm r).mem_iff.mp hbr
              exact ⟨⟨hba, before_append_of_mem ha_l (by simp [hb_r])⟩,
                m, hl a ha_l,
                before_append_of_mem ha_l (by simp),
                before_append_right (before_append_of_mem (l₁ := [m]) (by simp) hb_r)⟩
          · rintro ⟨⟨hba, hab⟩, c, hac, hac_b, hcb_b⟩
            have ha_mem : a ∈ l ++ m :: r := mem_of_before_left hab
            have hb_mem : b ∈ l ++ m :: r := mem_of_before_right hab
            have hc_mem : c ∈ l ++ m :: r := mem_of_before_right hac_b
            have ha_lt_m : a < m := Nat.lt_of_lt_of_le hac (hmax_all c hc_mem)
            have hb_lt_m : b < m := Nat.lt_trans hba ha_lt_m
            have hne_am : a ≠ m := by omega
            have hne_bm : b ≠ m := by omega
            simp only [List.mem_append, List.mem_cons] at ha_mem hb_mem
            rcases ha_mem with hal | rfl | har
            · rcases hb_mem with hbl | rfl | hbr
              · -- Both `a, b ∈ l`: `c` must also be in `l`!
                have hc_l : c ∈ l := by
                  rcases before_append_cases hnd hcb_b with h1 | h2 | ⟨hcl, _⟩
                  · exact mem_of_before_left h1
                  · exfalso
                    have hb_in_mr : b ∈ m :: r := mem_of_before_right h2
                    exact (List.nodup_append.mp hnd).2.2 b hbl b hb_in_mr rfl
                  · exact hcl
                have hab_l : Before l a b := by
                  rcases before_or_before hal hbl (by omega) with h | h
                  · exact h
                  · exact absurd (before_append_left h) (fun h' => before_asymm hnd hab h')
                have hac_l : Before l a c := by
                  rcases before_or_before hal hc_l (by omega) with h | h
                  · exact h
                  · exact absurd (before_append_left h) (fun h' => before_asymm hnd hac_b h')
                have hcb_l : Before l c b := by
                  rcases before_or_before hc_l hbl (by omega) with h | h
                  · exact h
                  · exact absurd (before_append_left h) (fun h' => before_asymm hnd hcb_b h')
                have hSl := (ih l hlen_l hnd_l a b).mpr ⟨⟨hba, hab_l⟩, c, hac, hac_l, hcb_l⟩
                exact ⟨hba, before_append_left (before_append_left hSl.2)⟩
              · omega
              · -- `a ∈ l`, `b ∈ r`: immediately `Before (westSort l ++ westSort r) a b`!
                have hal' : a ∈ westSort l := (westSort_perm l).mem_iff.mpr hal
                have hbr' : b ∈ westSort r := (westSort_perm r).mem_iff.mpr hbr
                exact ⟨hba, before_append_left (before_append_of_mem hal' hbr')⟩
            · omega
            · rcases hb_mem with hbl | rfl | hbr
              · exfalso
                exact before_asymm hnd hab (before_append_of_mem hbl (by simp [har]))
              · omega
              · -- Both `a, b ∈ r`: `c` must also be in `r`!
                have hc_r : c ∈ r := by
                  rcases before_append_cases hnd hac_b with h1 | h2 | ⟨hal, _⟩
                  · exfalso
                    exact (List.nodup_append.mp hnd).2.2 a (mem_of_before_left h1) a (by simp [har]) rfl
                  · have hc_mr : c ∈ m :: r := mem_of_before_right h2
                    simp only [List.mem_cons] at hc_mr
                    rcases hc_mr with hcm | hcr
                    · exfalso
                      rw [hcm] at h2
                      exact before_asymm hnd_mr h2 (before_append_of_mem (l₁ := [m]) (by simp) har)
                    · exact hcr
                  · exfalso
                    exact (List.nodup_append.mp hnd).2.2 a hal a (by simp [har]) rfl
                have hmr_before : ∀ u v, u ∈ r → v ∈ r → Before (l ++ m :: r) u v → Before r u v := by
                  intro u v hur hvr huv
                  have hne : u ≠ v := fun h => before_irrefl hnd (h ▸ huv)
                  rcases before_or_before hur hvr hne with h | h
                  · exact h
                  · exact absurd (before_append_right (before_append_right (l₁ := [m]) h))
                      (fun h' => before_asymm hnd huv h')
                have hSr := (ih r hlen_r hnd_r a b).mpr
                  ⟨⟨hba, hmr_before a b har hbr hab⟩, c, hac,
                    hmr_before a c har hc_r hac_b, hmr_before c b hc_r hbr hcb_b⟩
                exact ⟨hba, before_append_left (before_append_right hSr.2)⟩

/-- `westSort xs ≤_L xs` on any `Nodup` list. -/
theorem westSort_weakBruhat_self {xs : List Nat} (hnd : xs.Nodup) :
    WeakBruhatLe (westSort xs) xs := by
  intro a b h
  exact ((invSet_westSort_iff hnd a b).mp h).1

/-- Every descent bottom of `westSort xs` is a right-valley of `xs`. -/
theorem rightValley_of_isDesBot_westSort {xs : List Nat} (hnd : xs.Nodup) {b : Nat}
    (hdes : IsDesBot (westSort xs) b) : IsRightValley xs b := by
  have hnd_S : (westSort xs).Nodup := ((westSort_perm xs).nodup_iff).mpr hnd
  rcases hdes with ⟨a, hba, hadj_S⟩
  have hab_S : IsInv (westSort xs) a b := ⟨hba, before_of_adj hadj_S⟩
  obtain ⟨⟨_, hab⟩, c, hac, hac_b, hcb_b⟩ := (invSet_westSort_iff hnd a b).mp hab_S
  intro d hadj_bd
  have hbd : Before xs b d := before_of_adj hadj_bd
  have hne : b ≠ d := fun h => before_irrefl hnd (h ▸ hbd)
  by_cases hlt : b < d
  · exact hlt
  · exfalso
    have hdb : d < b := by omega
    have hnot_inv_bd : ¬ IsInv (westSort xs) b d := by
      intro hinv
      obtain ⟨_, w, _, hbw, hwd⟩ := (invSet_westSort_iff hnd b d).mp hinv
      exact ((adj_iff_before_no_between hnd).mp hadj_bd).2 w ⟨hbw, hwd⟩
    have hd_mem_S : d ∈ westSort xs := (westSort_perm xs).mem_iff.mpr (mem_of_before_right hbd)
    have hb_mem_S : b ∈ westSort xs := mem_of_before_right (before_of_adj hadj_S)
    have hdb_S : Before (westSort xs) d b := by
      rcases before_or_before hd_mem_S hb_mem_S (by omega) with h | h
      · exact h
      · exact absurd ⟨hdb, h⟩ hnot_inv_bd
    have ha_mem_S : a ∈ westSort xs := mem_of_before_left (before_of_adj hadj_S)
    have hda_S : Before (westSort xs) d a := by
      rcases before_or_before hd_mem_S ha_mem_S (by omega) with h | h
      · exact h
      · exact absurd ⟨h, hdb_S⟩ (((adj_iff_before_no_between hnd_S).mp hadj_S).2 d)
    have had_S : IsInv (westSort xs) a d := by
      rw [invSet_westSort_iff hnd a d]
      exact ⟨⟨by omega, before_trans hnd hab hbd⟩, c, hac, hac_b, before_trans hnd hcb_b hbd⟩
    exact before_asymm hnd_S hda_S had_S.2

/-- If `b` is a right-valley of `xs`, every right-inversion `(b, z)` of `xs` survives `westSort`. -/
theorem inv_rightValley_westSort {xs : List Nat} (hnd : xs.Nodup) {b z : Nat}
    (hrv : IsRightValley xs b) (hbz : IsInv xs b z) : IsInv (westSort xs) b z := by
  rw [invSet_westSort_iff hnd b z]
  refine ⟨hbz, ?_⟩
  rcases hbz with ⟨hzb, l₁, l₂, l₃, rfl⟩
  cases l₂ with
  | nil =>
      exfalso
      have hlt := hrv z ⟨l₁, l₃, by simp⟩
      omega
  | cons d l₂' =>
      have hbd : b < d := hrv d ⟨l₁, l₂' ++ z :: l₃, by simp [List.append_assoc]⟩
      refine ⟨d, hbd,
        ⟨l₁, [], l₂' ++ z :: l₃, by simp [List.append_assoc]⟩,
        ⟨l₁ ++ [b], l₂', l₃, by simp [List.append_assoc]⟩⟩

end WestTheory

section PopTheory

theorem popAux_perm : ∀ xs run : List Nat, (popAux xs run).Perm (xs ++ run)
  | [], run => by simp [popAux]
  | x :: xs, [] => by
      simp only [popAux]
      exact (popAux_perm xs [x]).trans (by simp [List.perm_append_singleton])
  | x :: xs, r :: rs => by
      simp only [popAux]
      split
      · exact (popAux_perm xs (x :: r :: rs)).trans (by
          simp only [List.cons_append]
          exact List.perm_middle (l₁ := xs) (l₂ := r :: rs) (a := x))
      · have ih := popAux_perm xs [x]
        have h1 : ((r :: rs) ++ popAux xs [x]).Perm ((r :: rs) ++ (xs ++ [x])) :=
          List.Perm.append_left (r :: rs) ih
        have h2 : ((r :: rs) ++ (xs ++ [x])).Perm ((xs ++ [x]) ++ (r :: rs)) :=
          List.perm_append_comm
        have h3 : ((xs ++ [x]) ++ (r :: rs)).Perm ((x :: xs) ++ (r :: rs)) :=
          List.Perm.append_right (r :: rs) (List.perm_append_singleton x xs)
        exact h1.trans (h2.trans h3)

theorem popSort_perm (xs : List Nat) : (popSort xs).Perm xs := by
  have h := popAux_perm xs []
  simp only [List.append_nil] at h
  exact h

/-- Splitting a nonempty list into its maximal strictly decreasing prefix and the remainder. -/
def splitRunAux (r : Nat) (acc : List Nat) : List Nat → List Nat × List Nat
  | [] => (r :: acc, [])
  | x :: xs =>
      if r > x then splitRunAux x (r :: acc) xs
      else (r :: acc, x :: xs)

theorem popAux_eq_splitRunAux (r : Nat) (acc : List Nat) : ∀ xs : List Nat,
    popAux xs (r :: acc) = (splitRunAux r acc xs).1 ++ popSort (splitRunAux r acc xs).2
  | [] => by simp [popAux, splitRunAux, popSort]
  | x :: xs => by
      simp only [popAux, splitRunAux]
      by_cases hrx : r > x
      · simp only [hrx, ↓reduceIte]
        exact popAux_eq_splitRunAux x (r :: acc) xs
      · simp only [hrx, ↓reduceIte, popSort, popAux]

/-- Properties of `splitRunAux`: reversing `acc` recovers the input, the prefix is strictly
decreasing, and if the remainder is nonempty its head is `≥` the last element of the prefix. -/
theorem splitRunAux_spec (r : Nat) (acc xs : List Nat)
    (hdec : StrictlyDec (acc.reverse ++ [r])) :
    let res := splitRunAux r acc xs
    (acc.reverse ++ r :: xs = res.1.reverse ++ res.2) ∧
    StrictlyDec res.1.reverse ∧
    (∀ y rest, res.2 = y :: rest → ¬ (r > y) ∨ ∃ last, res.1 = last :: res.1.tail ∧ ¬ (last > y)) ∧
    (∀ y rest, res.2 = y :: rest → ∃ last tail, res.1 = last :: tail ∧ ¬ (last > y)) := by
  induction xs generalizing r acc with
  | nil =>
      refine ⟨by simp [splitRunAux], ?_, by simp [splitRunAux], by simp [splitRunAux]⟩
      simpa [splitRunAux] using hdec
  | cons x xs' ih =>
      simp only [splitRunAux]
      by_cases hrx : r > x
      · simp only [hrx, ↓reduceIte]
        have hdec' : StrictlyDec ((r :: acc).reverse ++ [x]) := by
          have h1 : (r :: acc).reverse ++ [x] = (acc.reverse ++ [r]) ++ [x] := by simp [List.append_assoc]
          rw [h1]
          clear h1
          suffices hpush : ∀ l : List Nat, StrictlyDec (l ++ [r]) → x < r →
              StrictlyDec ((l ++ [r]) ++ [x]) from hpush acc.reverse hdec hrx
          intro l
          induction l with
          | nil => intro _ hlt; exact ⟨hlt, trivial⟩
          | cons u us ihu =>
              cases us with
              | nil => intro h1 hlt; exact ⟨h1.1, hlt, trivial⟩
              | cons v vs => intro h1 hlt; exact ⟨h1.1, ihu h1.2 hlt⟩
        obtain ⟨heq, hsd, _, hlast⟩ := ih x (r :: acc) hdec'
        refine ⟨?_, hsd, ?_, hlast⟩
        · simpa [List.append_assoc] using heq
        · intro y rest hy; right
          obtain ⟨last, tail, h1, h2⟩ := hlast y rest hy
          exact ⟨last, by rw [h1]; rfl, h2⟩
      · simp only [hrx, ↓reduceIte]
        refine ⟨by simp, by simpa using hdec, ?_, ?_⟩
        · intro y rest hy
          simp only [List.cons.injEq] at hy
          left; rw [← hy.1]; exact hrx
        · intro y rest hy
          simp only [List.cons.injEq] at hy
          exact ⟨r, acc, rfl, by rw [← hy.1]; exact hrx⟩

/-- Clean maximal descending run decomposition for any nonempty `Nodup` list `xs`:
either `xs` itself is `StrictlyDec` (so `popSort xs = xs.reverse`), OR `xs = run ++ rest` where
`run` is nonempty & `StrictlyDec`, `rest` is nonempty, `run.getLast < rest.head`, and
`popSort xs = run.reverse ++ popSort rest`. -/
theorem popSort_run_decomp {xs : List Nat} (hne : xs ≠ []) (hnd : xs.Nodup) :
    (StrictlyDec xs ∧ popSort xs = xs.reverse) ∨
    (∃ (run rest : List Nat) (u v : Nat) (hrun : run ≠ []) (hrest : rest ≠ []),
      xs = run ++ rest ∧
      StrictlyDec run ∧
      run.getLast hrun = u ∧
      rest.head hrest = v ∧
      u < v ∧
      popSort xs = run.reverse ++ popSort rest) := by
  cases xs with
  | nil => exact absurd rfl hne
  | cons x rest0 =>
      have hpop : popSort (x :: rest0) =
          (splitRunAux x [] rest0).1 ++ popSort (splitRunAux x [] rest0).2 := by
        simpa [popSort, popAux] using popAux_eq_splitRunAux x [] rest0
      obtain ⟨heq, hsd, _, hlast⟩ := splitRunAux_spec x [] rest0 (by simp [StrictlyDec])
      simp only [List.reverse_nil, List.nil_append] at heq
      cases hrem : (splitRunAux x [] rest0).2 with
      | nil =>
          left
          rw [hrem, List.append_nil] at heq
          have hrev : (splitRunAux x [] rest0).1 = (x :: rest0).reverse := by
            rw [heq, List.reverse_reverse]
          refine ⟨by rw [heq]; exact hsd, ?_⟩
          rw [hpop, hrem, hrev]; simp [popSort, popAux]
      | cons y tail =>
          right
          obtain ⟨last, ltail, hrun_eq, hnotgt⟩ := hlast y tail hrem
          have hrun_rev_ne : (splitRunAux x [] rest0).1.reverse ≠ [] := by
            rw [hrun_eq]; simp
          refine ⟨(splitRunAux x [] rest0).1.reverse, y :: tail, last, y,
            hrun_rev_ne, by simp, by rw [← hrem]; exact heq, hsd, ?_, rfl, ?_, ?_⟩
          · simp [hrun_eq]
          · -- `last ≠ y` from `Nodup`:
            have hne_ly : last ≠ y := by
              rw [heq, hrem, hrun_eq] at hnd
              simp only [List.reverse_cons] at hnd
              have hdisj := (List.nodup_append.mp hnd).2.2
              exact hdisj last (by simp) y List.mem_cons_self
            omega
          · rw [hpop, hrem, List.reverse_reverse]

/-- Reversing a list reverses `Before`. -/
theorem before_reverse_iff {l : List Nat} {a b : Nat} :
    Before l.reverse a b ↔ Before l b a := by
  constructor
  · rintro ⟨l₁, l₂, l₃, heq⟩
    refine ⟨l₃.reverse, l₂.reverse, l₁.reverse, ?_⟩
    have := congrArg List.reverse heq
    simpa [List.reverse_reverse, List.append_assoc] using this
  · rintro ⟨l₁, l₂, l₃, heq⟩
    refine ⟨l₃.reverse, l₂.reverse, l₁.reverse, ?_⟩
    have := congrArg List.reverse heq
    simpa [List.append_assoc] using this

/-- **Exact inversion-set characterization of pop-stack sorting (`P`):**
For any `Nodup` list `xs`, `(a, b) ∈ InvSet(popSort xs)` if and only if `(a, b) ∈ InvSet(xs)`
and there is an adjacent ascent `u < v` in the contiguous segment of `xs` from `a` to `b`. -/
theorem invSet_popSort_iff : ∀ {xs : List Nat}, xs.Nodup → ∀ (a b : Nat),
    IsInv (popSort xs) a b ↔ IsInv xs a b ∧ HasAscentBetween xs a b := by
  intro xs
  suffices hstrong : ∀ n : Nat, ∀ xs : List Nat, xs.length ≤ n → xs.Nodup → ∀ a b : Nat,
      IsInv (popSort xs) a b ↔ IsInv xs a b ∧ HasAscentBetween xs a b by
    exact hstrong xs.length xs (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
      intro xs hlen _ a b
      cases xs with
      | nil => simp [popSort, popAux, IsInv, Before]
      | cons _ _ => simp at hlen
  | succ n ih =>
      intro xs hlen hnd a b
      cases xs with
      | nil => simp [popSort, popAux, IsInv, Before]
      | cons x xs0 =>
          rcases popSort_run_decomp (by simp : x :: xs0 ≠ []) hnd with
            ⟨hdec, hpop⟩ | ⟨run, rest, u, v, hrun_ne, hrest_ne, heq, hdec, hu, hv, huv, hpop⟩
          · -- Single strictly decreasing run: `popSort xs = xs.reverse`, ZERO inversions!
            rw [hpop]
            constructor
            · intro ⟨hba, hbef⟩
              exfalso
              have hbef_ba : Before (x :: xs0) b a := before_reverse_iff.mp hbef
              have hab : a < b := strictlyDec_before_gt hdec hbef_ba
              omega
            · rintro ⟨_, ⟨l₁, l₂, l₃, u, v, heq, huv, hadj⟩⟩
              exfalso
              rw [heq] at hdec
              have hdec1 : StrictlyDec (a :: l₂ ++ b :: l₃) :=
                strictlyDec_append_right (by simpa [List.append_assoc] using hdec)
              have hdec2 : StrictlyDec (a :: l₂ ++ [b]) :=
                strictlyDec_append_left (by simpa [List.append_assoc] using hdec1)
              exact strictlyDec_no_adj_ascent hdec2 hadj huv
          · -- Split into maximal descending `run` and nonempty `rest` with `u < v` at the boundary!
            rw [heq] at hlen hnd hpop ⊢
            rw [hpop]
            have hrun_pos : 0 < run.length := by cases run <;> simp at hrun_ne ⊢
            have hrest_len : rest.length ≤ n := by simp at hlen; omega
            have hnd_run : run.Nodup := (List.nodup_append.mp hnd).1
            have hnd_rest : rest.Nodup := (List.nodup_append.mp hnd).2.1
            have hnd_P : (run.reverse ++ popSort rest).Nodup := by
              have hperm : (run.reverse ++ popSort rest).Perm (run ++ rest) :=
                (List.reverse_perm run).append (popSort_perm rest)
              exact (hperm.nodup_iff).mpr hnd
            -- Write `run = run.dropLast ++ [u]` and `rest = v :: rest.tail`:
            have hrun_split : run = run.dropLast ++ [u] := by
              rw [← hu]; exact list_eq_dropLast_append_getLast run hrun_ne
            obtain ⟨v', rtail, hrest_eq⟩ : ∃ v' rtail, rest = v' :: rtail := by
              cases rest with
              | nil => exact absurd rfl hrest_ne
              | cons v' rtail => exact ⟨v', rtail, rfl⟩
            have hv' : v' = v := by simp [hrest_eq] at hv; exact hv
            rw [hv'] at hrest_eq
            constructor
            · intro ⟨hba, hbef⟩
              rcases before_append_cases hnd_P hbef with h1 | h2 | ⟨ha_rr, hb_pr⟩
              · exfalso
                have hbef_ba : Before run b a := before_reverse_iff.mp h1
                have hab : a < b := strictlyDec_before_gt hdec hbef_ba
                omega
              · obtain ⟨⟨_, hab_r⟩, hasc_r⟩ := (ih rest hrest_len hnd_rest a b).mp ⟨hba, h2⟩
                rcases hasc_r with ⟨p₁, p₂, p₃, u', v', hp, huv', hadj'⟩
                refine ⟨⟨hba, before_append_right hab_r⟩,
                  ⟨run ++ p₁, p₂, p₃, u', v', by rw [hp]; simp [List.append_assoc], huv', hadj'⟩⟩
              · have ha_run : a ∈ run := List.mem_reverse.mp ha_rr
                have hb_rest : b ∈ rest := (popSort_perm rest).mem_iff.mp hb_pr
                -- `u < v` lies in the contiguous segment from `a` to `b`!
                obtain ⟨p₁, p₂, hp⟩ := List.append_of_mem ha_run
                obtain ⟨q₁, q₂, hq⟩ := List.append_of_mem hb_rest
                -- Wait: split `a :: p₂` at `u` (its last element) and `q₁ ++ [b]` at `v` (its first element):
                have hseg : a :: (p₂ ++ q₁) ++ [b] = (a :: p₂) ++ (q₁ ++ [b]) := by
                  simp [List.append_assoc]
                have hadj_uv : Adj (a :: (p₂ ++ q₁) ++ [b]) u v := by
                  have hne_ap2 : a :: p₂ ≠ [] := by simp
                  have hlast_ap2 : (a :: p₂).getLast hne_ap2 = u := by
                    have h1 : run.getLast hrun_ne = (a :: p₂).getLast hne_ap2 := by
                      have : run = p₁ ++ a :: p₂ := hp
                      subst this
                      exact List.getLast_append_of_ne_nil hrun_ne hne_ap2
                    rw [← h1, hu]
                  have hsplit_ap2 : a :: p₂ = (a :: p₂).dropLast ++ [u] := by
                    rw [← hlast_ap2]; exact list_eq_dropLast_append_getLast (a :: p₂) hne_ap2
                  have hq1_head : q₁ ++ [b] = v :: (q₁ ++ [b]).tail := by
                    cases q₁ with
                    | nil =>
                        simp only [List.nil_append] at hq ⊢
                        rw [hrest_eq] at hq
                        simp only [List.cons.injEq] at hq
                        rw [hq.1]; rfl
                    | cons w q₁' =>
                        simp only [List.cons_append] at hq ⊢
                        rw [hrest_eq] at hq
                        simp only [List.cons.injEq] at hq
                        rw [hq.1]; rfl
                  refine ⟨(a :: p₂).dropLast, (q₁ ++ [b]).tail, ?_⟩
                  rw [hseg, hsplit_ap2, hq1_head]
                  simp [List.append_assoc]
                refine ⟨⟨hba, before_append_of_mem ha_run hb_rest⟩,
                  ⟨p₁, p₂ ++ q₁, q₂, u, v, ?_, huv, hadj_uv⟩⟩
                rw [hp, hq]; simp [List.append_assoc]
            · rintro ⟨⟨hba, hab⟩, hasc⟩
              rcases before_append_cases hnd hab with h1 | h2 | ⟨ha_run, hb_rest⟩
              · -- Both `a, b ∈ run`: impossible because `run` is `StrictlyDec`!
                exfalso
                rcases h1 with ⟨p₁, p₂, p₃, hp⟩
                have hnd_eq : (p₁ ++ a :: p₂ ++ b :: (p₃ ++ rest)).Nodup := by
                  simpa [hp, List.append_assoc] using hnd
                have hasc' : HasAscentBetween (p₁ ++ a :: p₂ ++ b :: (p₃ ++ rest)) a b := by
                  simpa [hp, List.append_assoc] using hasc
                have hnotdec := (hasAscentBetween_iff_not_strictlyDec hnd_eq).mp hasc'
                rw [hp] at hdec
                have hdec1 : StrictlyDec (a :: p₂ ++ b :: p₃) :=
                  strictlyDec_append_right (by simpa [List.append_assoc] using hdec)
                have hdec2 : StrictlyDec (a :: p₂ ++ [b]) :=
                  strictlyDec_append_left (by simpa [List.append_assoc] using hdec1)
                exact hnotdec hdec2
              · -- Both `a, b ∈ rest`:
                rcases h2 with ⟨p₁, p₂, p₃, hp⟩
                have hnd_eq : ((run ++ p₁) ++ a :: p₂ ++ b :: p₃).Nodup := by
                  simpa [hp, List.append_assoc] using hnd
                have hasc' : HasAscentBetween ((run ++ p₁) ++ a :: p₂ ++ b :: p₃) a b := by
                  simpa [hp, List.append_assoc] using hasc
                have hnotdec := (hasAscentBetween_iff_not_strictlyDec hnd_eq).mp hasc'
                have hasc_rest : HasAscentBetween rest a b := by
                  rw [hp]
                  exact (hasAscentBetween_iff_not_strictlyDec (by rw [← hp]; exact hnd_rest)).mpr hnotdec
                have hPr := (ih rest hrest_len hnd_rest a b).mpr
                  ⟨⟨hba, ⟨p₁, p₂, p₃, hp⟩⟩, hasc_rest⟩
                exact ⟨hba, before_append_right hPr.2⟩
              · -- `a ∈ run, b ∈ rest`: immediately `Before (run.reverse ++ popSort rest) a b`!
                exact ⟨hba, before_append_of_mem (List.mem_reverse.mpr ha_run)
                  ((popSort_perm rest).mem_iff.mpr hb_rest)⟩

/-- `popSort xs ≤_L xs` on any `Nodup` list. -/
theorem popSort_weakBruhat_self {xs : List Nat} (hnd : xs.Nodup) :
    WeakBruhatLe (popSort xs) xs := by
  intro a b h
  exact ((invSet_popSort_iff hnd a b).mp h).1

/-- Every descent bottom of `popSort xs` is a right-valley of `xs`. -/
theorem rightValley_of_isDesBot_popSort {xs : List Nat} (hnd : xs.Nodup) {b : Nat}
    (hdes : IsDesBot (popSort xs) b) : IsRightValley xs b := by
  have hnd_P : (popSort xs).Nodup := ((popSort_perm xs).nodup_iff).mpr hnd
  rcases hdes with ⟨a, hba, hadj_P⟩
  have hab_P : IsInv (popSort xs) a b := ⟨hba, before_of_adj hadj_P⟩
  obtain ⟨⟨_, hab⟩, hasc_ab⟩ := (invSet_popSort_iff hnd a b).mp hab_P
  intro d hadj_bd
  have hbd : Before xs b d := before_of_adj hadj_bd
  have hne : b ≠ d := fun h => before_irrefl hnd (h ▸ hbd)
  by_cases hlt : b < d
  · exact hlt
  · exfalso
    have hdb : d < b := by omega
    have hnot_inv_bd : ¬ IsInv (popSort xs) b d := by
      intro hinv
      obtain ⟨_, hasc_bd⟩ := (invSet_popSort_iff hnd b d).mp hinv
      rcases hadj_bd with ⟨l₁, l₂, rfl⟩
      have hnd' : (l₁ ++ b :: [] ++ d :: l₂).Nodup := by simpa using hnd
      have hnotdec := (hasAscentBetween_iff_not_strictlyDec hnd').mp (by simpa using hasc_bd)
      exact hnotdec ⟨hdb, trivial⟩
    have hd_mem_P : d ∈ popSort xs := (popSort_perm xs).mem_iff.mpr (mem_of_before_right hbd)
    have hb_mem_P : b ∈ popSort xs := mem_of_before_right (before_of_adj hadj_P)
    have hdb_P : Before (popSort xs) d b := by
      rcases before_or_before hd_mem_P hb_mem_P (by omega) with h | h
      · exact h
      · exact absurd ⟨hdb, h⟩ hnot_inv_bd
    have ha_mem_P : a ∈ popSort xs := mem_of_before_left (before_of_adj hadj_P)
    have hda_P : Before (popSort xs) d a := by
      rcases before_or_before hd_mem_P ha_mem_P (by omega) with h | h
      · exact h
      · exact absurd ⟨h, hdb_P⟩ (((adj_iff_before_no_between hnd_P).mp hadj_P).2 d)
    have had_P : IsInv (popSort xs) a d := by
      rw [invSet_popSort_iff hnd a d]
      exact ⟨⟨by omega, before_trans hnd hab hbd⟩, hasAscentBetween_extend_right hnd hasc_ab hbd⟩
    exact before_asymm hnd_P hda_P had_P.2

/-- If `b` is a right-valley of `xs`, every right-inversion `(b, z)` of `xs` survives `popSort`. -/
theorem inv_rightValley_popSort {xs : List Nat} (hnd : xs.Nodup) {b z : Nat}
    (hrv : IsRightValley xs b) (hbz : IsInv xs b z) : IsInv (popSort xs) b z := by
  rw [invSet_popSort_iff hnd b z]
  refine ⟨hbz, ?_⟩
  rcases hbz with ⟨hzb, l₁, l₂, l₃, rfl⟩
  cases l₂ with
  | nil =>
      exfalso
      have hlt := hrv z ⟨l₁, l₃, by simp⟩
      omega
  | cons d l₂' =>
      have hbd : b < d := hrv d ⟨l₁, l₂' ++ z :: l₃, by simp [List.append_assoc]⟩
      exact ⟨l₁, d :: l₂', l₃, b, d, rfl, hbd, [], l₂' ++ [z], by simp⟩

end PopTheory

end WeakBruhatCommutators
