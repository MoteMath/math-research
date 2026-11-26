/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakBruhatCommutators.Basic

/-!
# Exact Set-Theoretic Theory of Bubble Sort (`invSet_bubblePass_iff`, `desBot_bubblePass_iff`)

Proves the complete set-theoretic characterization of `bubblePass`:
- `invSet_bubblePass_iff`: `IsInv (bubblePass xs) a b ↔ IsInv xs a b ∧ ∃ c, a < c ∧ IsInv xs c b`
- `desBot_bubblePass_iff`: `IsDesBot (bubblePass xs) b ↔ IsDesBot xs b ∧ 2 ≤ leftInv xs b`
- `invSet_bubblePass_mono`: `WeakBruhatLe xs ys → WeakBruhatLe (bubblePass xs) (bubblePass ys)`
- `bubbleOrder_bubblePass_mono`: `BubbleLe xs ys → BubbleLe (bubblePass xs) (bubblePass ys)`
- Plus right-valley preservation and the `DesBot(B)` witness-transfer lemma.
-/

namespace WeakBruhatCommutators

section BubbleCore

/-- Running maximum starting from `m` across a list `l`. -/
def listMax (m : Nat) : List Nat → Nat
  | [] => m
  | x :: xs => listMax (if m > x then m else x) xs

theorem le_listMax (m : Nat) : ∀ l : List Nat, m ≤ listMax m l
  | [] => Nat.le_refl m
  | x :: xs => by
      simp only [listMax]
      have h := le_listMax (if m > x then m else x) xs
      by_cases hmx : m > x <;> simp only [hmx, ↓reduceIte] at h ⊢ <;> omega

theorem mem_le_listMax (m : Nat) : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ listMax m l
  | [], _, h => by simp at h
  | y :: ys, x, h => by
      simp only [List.mem_cons] at h
      simp only [listMax]
      rcases h with rfl | hy
      · have h1 := le_listMax (if m > x then m else x) ys
        by_cases hmx : m > x <;> simp only [hmx, ↓reduceIte] at h1 ⊢ <;> omega
      · exact mem_le_listMax _ hy

theorem listMax_mem (m : Nat) : ∀ l : List Nat, listMax m l ∈ m :: l
  | [] => by simp [listMax]
  | x :: xs => by
      simp only [listMax]
      by_cases h : m > x
      · simp only [h, ↓reduceIte]
        have hm := listMax_mem m xs
        simp only [List.mem_cons] at hm ⊢
        rcases hm with hm1 | hm'
        · exact Or.inl hm1
        · exact Or.inr (Or.inr hm')
      · simp only [h, ↓reduceIte]
        have hm := listMax_mem x xs
        simp only [List.mem_cons] at hm ⊢
        rcases hm with hm1 | hm'
        · exact Or.inr (Or.inl hm1)
        · exact Or.inr (Or.inr hm')

theorem listMax_gt_iff (m a : Nat) (l : List Nat) :
    a < listMax m l ↔ a < m ∨ ∃ c ∈ l, a < c := by
  constructor
  · intro hlt
    have hm := listMax_mem m l
    simp only [List.mem_cons] at hm
    rcases hm with heq | hmem
    · left; rw [← heq]; exact hlt
    · right; exact ⟨listMax m l, hmem, hlt⟩
  · rintro (hm | ⟨c, hc, hlt⟩)
    · exact Nat.lt_of_lt_of_le hm (le_listMax m l)
    · exact Nat.lt_of_lt_of_le hlt (mem_le_listMax m hc)

theorem bubbleCarry_perm (m : Nat) : ∀ xs : List Nat, (bubbleCarry m xs).Perm (m :: xs)
  | [] => List.Perm.refl _
  | y :: rest => by
      simp only [bubbleCarry]
      split
      · exact (List.Perm.cons y (bubbleCarry_perm m rest)).trans (List.Perm.swap m y rest)
      · exact List.Perm.cons m (bubbleCarry_perm y rest)

theorem bubblePass_perm : ∀ xs : List Nat, (bubblePass xs).Perm xs
  | [] => List.Perm.refl _
  | x :: xs => bubbleCarry_perm x xs

theorem iterBubble_perm (k : Nat) (xs : List Nat) : (iterBubble k xs).Perm xs := by
  induction k with
  | zero => exact List.Perm.refl xs
  | succ k ih => exact (bubblePass_perm _).trans ih

/-- Core prefix-splitting identity for `bubbleCarry`: processing `l₁` emits a prefix `out`
such that `(out ++ [listMax m l₁]).Perm (m :: l₁)` and continues with `bubbleCarry (listMax m l₁) l₂`. -/
theorem bubbleCarry_append (m : Nat) : ∀ (l₁ l₂ : List Nat),
    ∃ out, bubbleCarry m (l₁ ++ l₂) = out ++ bubbleCarry (listMax m l₁) l₂ ∧
           (out ++ [listMax m l₁]).Perm (m :: l₁)
  | [], l₂ => ⟨[], by simp [listMax], List.Perm.refl _⟩
  | x :: l₁', l₂ => by
      simp only [List.cons_append, bubbleCarry, listMax]
      by_cases h : m > x
      · simp only [h, ↓reduceIte]
        obtain ⟨out, heq, hperm⟩ := bubbleCarry_append m l₁' l₂
        refine ⟨x :: out, by simp [heq], ?_⟩
        exact (List.Perm.cons x hperm).trans (List.Perm.swap m x l₁')
      · simp only [h, ↓reduceIte]
        obtain ⟨out, heq, hperm⟩ := bubbleCarry_append x l₁' l₂
        refine ⟨m :: out, by simp [heq], List.Perm.cons m hperm⟩

/-- Variant tracking the exact last element of `out` when `l₁` is nonempty and `m` is exceeded. -/
theorem bubbleCarry_last_of_gt_head (m : Nat) : ∀ (l₁ : List Nat) (x : Nat) (l₂ : List Nat),
    listMax m l₁ < x →
    ∃ p, bubbleCarry m (l₁ ++ x :: l₂) = p ++ [listMax m l₁] ++ bubbleCarry x l₂ ∧
         (p ++ [listMax m l₁]).Perm (m :: l₁) := by
  intro l₁ x l₂ hlt
  obtain ⟨out, heq, hperm⟩ := bubbleCarry_append m l₁ (x :: l₂)
  simp only [bubbleCarry] at heq
  have hnot : ¬ listMax m l₁ > x := by omega
  simp only [hnot, ↓reduceIte] at heq
  refine ⟨out, by simpa [List.append_assoc] using heq, hperm⟩

/-- On any `Nodup` list `xs`, `bubblePass` never creates a new inversion (`B(xs) ≤_L xs`). -/
theorem bubblePass_weakBruhat_self {xs : List Nat} (hnd : xs.Nodup) :
    WeakBruhatLe (bubblePass xs) xs := by
  intro a b ⟨hba, hbef⟩
  refine ⟨hba, ?_⟩
  have ha : a ∈ xs := (bubblePass_perm xs).mem_iff.mp (mem_of_before_left hbef)
  have hb : b ∈ xs := (bubblePass_perm xs).mem_iff.mp (mem_of_before_right hbef)
  rcases before_or_before ha hb (by omega) with hab | hba'
  · exact hab
  · exfalso
    -- If `b` appeared before `a` in `xs` with `b < a`, `b` stays before `a` in `bubblePass xs`!
    rcases hba' with ⟨l₁, l₂, l₃, rfl⟩
    have hnd_B : (bubblePass (l₁ ++ b :: l₂ ++ a :: l₃)).Nodup :=
      ((bubblePass_perm _).nodup_iff).mpr hnd
    have hbef_ba : Before (bubblePass (l₁ ++ b :: l₂ ++ a :: l₃)) b a := by
      cases l₁ with
      | nil =>
          simp only [List.nil_append, List.cons_append, bubblePass]
          obtain ⟨out, heq, hperm⟩ := bubbleCarry_append b l₂ (a :: l₃)
          rw [heq]
          have ha_in : a ∈ bubbleCarry (listMax b l₂) (a :: l₃) :=
            (bubbleCarry_perm _ _).mem_iff.mpr (by simp)
          by_cases hbm : listMax b l₂ = b
          · rw [hbm]
            simp only [bubbleCarry]
            have hnot : ¬ b > a := by omega
            simp only [hnot, ↓reduceIte]
            have ha_in' : a ∈ bubbleCarry a l₃ := (bubbleCarry_perm a l₃).mem_iff.mpr (by simp)
            obtain ⟨q₁, q₂, hq⟩ := List.append_of_mem ha_in'
            exact before_append_right ⟨[], q₁, q₂, by rw [hq]; simp⟩
          · have hb_in_out : b ∈ out := by
              have hb_in : b ∈ out ++ [listMax b l₂] := hperm.mem_iff.mpr (by simp)
              simp only [List.mem_append, List.mem_singleton] at hb_in
              rcases hb_in with h | h
              · exact h
              · exact absurd h.symm hbm
            exact before_append_of_mem hb_in_out ha_in
      | cons x l₁' =>
          simp only [List.cons_append, bubblePass]
          obtain ⟨out1, heq1, hperm1⟩ := bubbleCarry_append x (l₁' ++ [b] ++ l₂) (a :: l₃)
          have heq' : x :: (l₁' ++ b :: (l₂ ++ a :: l₃)) = x :: ((l₁' ++ [b] ++ l₂) ++ a :: l₃) := by
            simp [List.append_assoc]
          have heq1' : bubbleCarry x (l₁' ++ b :: l₂ ++ a :: l₃) =
              out1 ++ bubbleCarry (listMax x (l₁' ++ [b] ++ l₂)) (a :: l₃) := by
            simpa [List.append_assoc] using heq1
          rw [heq1']
          have ha_in : a ∈ bubbleCarry (listMax x (l₁' ++ [b] ++ l₂)) (a :: l₃) :=
            (bubbleCarry_perm _ _).mem_iff.mpr (by simp)
          by_cases hbm : listMax x (l₁' ++ [b] ++ l₂) = b
          · rw [hbm]
            simp only [bubbleCarry]
            have hnot : ¬ b > a := by omega
            simp only [hnot, ↓reduceIte]
            have ha_in' : a ∈ bubbleCarry a l₃ := (bubbleCarry_perm a l₃).mem_iff.mpr (by simp)
            obtain ⟨q₁, q₂, hq⟩ := List.append_of_mem ha_in'
            exact before_append_right ⟨[], q₁, q₂, by rw [hq]; simp⟩
          · have hb_in_out : b ∈ out1 := by
              have hb_in : b ∈ out1 ++ [listMax x (l₁' ++ [b] ++ l₂)] :=
                hperm1.mem_iff.mpr (by simp)
              simp only [List.mem_append, List.mem_singleton] at hb_in
              rcases hb_in with h | h
              · exact h
              · exact absurd h.symm hbm
            exact before_append_of_mem hb_in_out ha_in
    exact before_asymm hnd_B hbef hbef_ba

/-- **Theorem 1 (`invSet_bubblePass_iff`):** Exact set-theoretic characterization of `bubblePass`
in Left Weak Bruhat Order: for any `Nodup` list `xs`,
`IsInv (bubblePass xs) a b ↔ IsInv xs a b ∧ ∃ c, a < c ∧ IsInv xs c b`. -/
theorem invSet_bubblePass_iff {xs : List Nat} (hnd : xs.Nodup) (a b : Nat) :
    IsInv (bubblePass xs) a b ↔ IsInv xs a b ∧ ∃ c, a < c ∧ IsInv xs c b := by
  have hnd_B : (bubblePass xs).Nodup := ((bubblePass_perm xs).nodup_iff).mpr hnd
  constructor
  · intro hB
    have hxs : IsInv xs a b := bubblePass_weakBruhat_self hnd a b hB
    refine ⟨hxs, ?_⟩
    rcases hxs with ⟨hba, ⟨l₁, l₂, l₃, rfl⟩⟩
    -- Split `bubblePass (l₁ ++ a :: l₂ ++ b :: l₃)` at `b`:
    cases l₁ with
    | nil =>
        simp only [List.nil_append, List.cons_append, bubblePass] at hB hnd hnd_B ⊢
        obtain ⟨out, heq, hperm⟩ := bubbleCarry_append a l₂ (b :: l₃)
        by_cases hgt : a < listMax a l₂
        · obtain ⟨c, hc, hac⟩ := (listMax_gt_iff a a l₂).mp hgt |>.resolve_left (by omega)
          exact ⟨c, hac, Nat.lt_trans hba hac,
            before_append_of_mem (by simp [hc] : c ∈ a :: l₂) (by simp : b ∈ b :: l₃)⟩
        · exfalso
          have hle : listMax a l₂ ≤ a := by omega
          have heq_m : listMax a l₂ = a := Nat.le_antisymm hle (le_listMax a l₂)
          rw [heq, heq_m] at hB hnd_B
          simp only [bubbleCarry, hba, ↓reduceIte] at hB hnd_B
          have ha_in : a ∈ bubbleCarry a l₃ := (bubbleCarry_perm a l₃).mem_iff.mpr (by simp)
          have hbef_ba : Before (out ++ b :: bubbleCarry a l₃) b a := by
            obtain ⟨q₁, q₂, hq⟩ := List.append_of_mem ha_in
            exact ⟨out, q₁, q₂, by rw [hq]; simp⟩
          exact before_asymm hnd_B hB.2 hbef_ba
    | cons x l₁' =>
        simp only [List.cons_append, bubblePass] at hB hnd hnd_B ⊢
        obtain ⟨out, heq, hperm⟩ := bubbleCarry_append x (l₁' ++ [a] ++ l₂) (b :: l₃)
        have heq' : bubbleCarry x (l₁' ++ a :: l₂ ++ b :: l₃) =
            out ++ bubbleCarry (listMax x (l₁' ++ [a] ++ l₂)) (b :: l₃) := by
          simpa [List.append_assoc] using heq
        by_cases hgt : a < listMax x (l₁' ++ [a] ++ l₂)
        · rcases (listMax_gt_iff x a (l₁' ++ [a] ++ l₂)).mp hgt with hax | ⟨c, hc, hac⟩
          · exact ⟨x, hax, Nat.lt_trans hba hax, ⟨[], l₁' ++ a :: l₂, l₃, by simp [List.append_assoc]⟩⟩
          · simp only [List.mem_append, List.mem_singleton] at hc
            rcases hc with (hc1 | rfl) | hc2
            · obtain ⟨p₁, p₂, rfl⟩ := List.append_of_mem hc1
              exact ⟨c, hac, Nat.lt_trans hba hac,
                ⟨x :: p₁, p₂ ++ a :: l₂, l₃, by simp [List.append_assoc]⟩⟩
            · omega
            · obtain ⟨p₁, p₂, rfl⟩ := List.append_of_mem hc2
              exact ⟨c, hac, Nat.lt_trans hba hac,
                ⟨x :: l₁' ++ a :: p₁, p₂, l₃, by simp [List.append_assoc]⟩⟩
        · exfalso
          have ha_le : a ≤ listMax x (l₁' ++ [a] ++ l₂) := mem_le_listMax x (by simp)
          have heq_m : listMax x (l₁' ++ [a] ++ l₂) = a := by omega
          rw [heq', heq_m] at hB hnd_B
          simp only [bubbleCarry, hba, ↓reduceIte] at hB hnd_B
          have ha_in : a ∈ bubbleCarry a l₃ := (bubbleCarry_perm a l₃).mem_iff.mpr (by simp)
          have hbef_ba : Before (out ++ b :: bubbleCarry a l₃) b a := by
            obtain ⟨q₁, q₂, hq⟩ := List.append_of_mem ha_in
            exact ⟨out, q₁, q₂, by rw [hq]; simp⟩
          exact before_asymm hnd_B hB.2 hbef_ba
  · rintro ⟨⟨hba, ⟨l₁, l₂, l₃, rfl⟩⟩, c, hac, ⟨hcb, hbef_cb⟩⟩
    refine ⟨hba, ?_⟩
    -- `c` precedes `b`, so `c ∈ l₁ ++ a :: l₂`!
    have hc_in_pref : c ∈ l₁ ++ a :: l₂ := by
      have hnd' : ((l₁ ++ a :: l₂) ++ b :: l₃).Nodup := by simpa [List.append_assoc] using hnd
      rcases before_append_cases hnd' (by simpa [List.append_assoc] using hbef_cb) with h1 | h2 | ⟨hc, _⟩
      · exact mem_of_before_left h1
      · exfalso
        have hnd2 : (b :: l₃).Nodup := (List.nodup_append.mp hnd').2.1
        rcases h2 with ⟨p₁, p₂, p₃, heq⟩
        cases p₁ with
        | nil =>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
            rcases heq with ⟨rfl, _⟩; omega
        | cons y p₁' =>
            simp only [List.cons_append, List.cons.injEq] at heq
            have : b ∉ l₃ := (List.nodup_cons.mp hnd2).1
            rw [heq.2] at this; exact this (by simp)
      · exact hc
    cases l₁ with
    | nil =>
        simp only [List.nil_append, List.cons_append, bubblePass]
        obtain ⟨out, heq, hperm⟩ := bubbleCarry_append a l₂ (b :: l₃)
        rw [heq]
        have hm_gt : a < listMax a l₂ := by
          simp only [List.nil_append, List.mem_cons] at hc_in_pref
          rcases hc_in_pref with rfl | hc2
          · omega
          · exact Nat.lt_of_lt_of_le hac (mem_le_listMax a hc2)
        have ha_in_out : a ∈ out := by
          have ha_in : a ∈ out ++ [listMax a l₂] := hperm.mem_iff.mpr (by simp)
          simp only [List.mem_append, List.mem_singleton] at ha_in
          rcases ha_in with h | h
          · exact h
          · omega
        have hb_in : b ∈ bubbleCarry (listMax a l₂) (b :: l₃) :=
          (bubbleCarry_perm _ _).mem_iff.mpr (by simp)
        exact before_append_of_mem ha_in_out hb_in
    | cons x l₁' =>
        simp only [List.cons_append, bubblePass]
        obtain ⟨out, heq, hperm⟩ := bubbleCarry_append x (l₁' ++ [a] ++ l₂) (b :: l₃)
        have heq' : bubbleCarry x (l₁' ++ a :: l₂ ++ b :: l₃) =
            out ++ bubbleCarry (listMax x (l₁' ++ [a] ++ l₂)) (b :: l₃) := by
          simpa [List.append_assoc] using heq
        rw [heq']
        have hm_gt : a < listMax x (l₁' ++ [a] ++ l₂) := by
          simp only [List.cons_append, List.mem_cons, List.mem_append] at hc_in_pref
          rcases hc_in_pref with rfl | hc1 | rfl | hc2
          · exact Nat.lt_of_lt_of_le hac (le_listMax c _)
          · exact Nat.lt_of_lt_of_le hac (mem_le_listMax x (by simp [hc1]))
          · omega
          · exact Nat.lt_of_lt_of_le hac (mem_le_listMax x (by simp [hc2]))
        have ha_in_out : a ∈ out := by
          have ha_in : a ∈ out ++ [listMax x (l₁' ++ [a] ++ l₂)] := hperm.mem_iff.mpr (by simp)
          simp only [List.mem_append, List.mem_singleton] at ha_in
          rcases ha_in with h | h
          · exact h
          · omega
        have hb_in : b ∈ bubbleCarry (listMax x (l₁' ++ [a] ++ l₂)) (b :: l₃) :=
          (bubbleCarry_perm _ _).mem_iff.mpr (by simp)
        exact before_append_of_mem ha_in_out hb_in

/-- **Theorem 2 (`invSet_bubblePass_mono`):** Single-pass bubble sort is monotone in Left Weak
Bruhat Order! -/
theorem invSet_bubblePass_mono {xs ys : List Nat} (hnd_x : xs.Nodup) (hnd_y : ys.Nodup)
    (hle : WeakBruhatLe xs ys) :
    WeakBruhatLe (bubblePass xs) (bubblePass ys) := by
  intro a b h
  rw [invSet_bubblePass_iff hnd_x] at h
  rw [invSet_bubblePass_iff hnd_y]
  rcases h with ⟨hab, c, hac, hcb⟩
  exact ⟨hle a b hab, c, hac, hle c b hcb⟩

end BubbleCore

section BubbleDesBot

/-- When `m ∉ l`, every element preceding `m` in `bubbleCarry m l` is strictly `< m`. -/
theorem bubbleCarry_before_lt (m : Nat) : ∀ {l : List Nat}, m ∉ l → ∀ {a : Nat},
    Before (bubbleCarry m l) a m → a < m := by
  intro l
  induction l with
  | nil =>
      intro _ a h
      rcases h with ⟨l₁, l₂, l₃, heq⟩
      cases l₁ <;> simp [bubbleCarry] at heq
  | cons y rest ih =>
      intro hm a h
      have hmy_ne : m ≠ y := fun heq => hm (by simp [heq])
      have hm_rest : m ∉ rest := fun h' => hm (by simp [h'])
      simp only [bubbleCarry] at h
      by_cases hmy : m > y
      · simp only [hmy, ↓reduceIte] at h
        rcases h with ⟨l₁, l₂, l₃, heq⟩
        cases l₁ with
        | nil =>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
            rcases heq with ⟨rfl, _⟩
            exact hmy
        | cons z l₁' =>
            simp only [List.cons_append, List.cons.injEq] at heq
            exact ih hm_rest ⟨l₁', l₂, l₃, heq.2⟩
      · simp only [hmy, ↓reduceIte] at h
        exfalso
        rcases h with ⟨l₁, l₂, l₃, heq⟩
        cases l₁ with
        | nil =>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
            rcases heq with ⟨rfl, htail⟩
            have hm_in : m ∈ bubbleCarry y rest := by rw [htail]; simp
            have hm_in' : m ∈ y :: rest := (bubbleCarry_perm y rest).mem_iff.mp hm_in
            simp only [List.mem_cons] at hm_in'
            rcases hm_in' with heq' | h'
            · exact hmy_ne heq'
            · exact hm_rest h'
        | cons z l₁' =>
            simp only [List.cons_append, List.cons.injEq] at heq
            have hm_in : m ∈ bubbleCarry y rest := by rw [heq.2]; simp
            have hm_in' : m ∈ y :: rest := (bubbleCarry_perm y rest).mem_iff.mp hm_in
            simp only [List.mem_cons] at hm_in'
            rcases hm_in' with heq' | h'
            · exact hmy_ne heq'
            · exact hm_rest h'

/-- On a `Nodup` list, if `b` is a left-to-right max (no `a > b` precedes `b`), `b` is NOT a
descent bottom of `bubblePass xs`. -/
theorem not_isDesBot_bubblePass_of_no_inv {xs : List Nat} (hnd : xs.Nodup) {b : Nat}
    (hno : ∀ a, ¬ IsInv xs a b) : ¬ IsDesBot (bubblePass xs) b := by
  rintro ⟨a, hba, hadj⟩
  have hinv : IsInv (bubblePass xs) a b := ⟨hba, before_of_adj hadj⟩
  exact hno a (bubblePass_weakBruhat_self hnd a b hinv)

/-- Unique predecessor in `Adj`: on a `Nodup` list, if `Adj xs a₁ b` and `Adj xs a₂ b` then `a₁ = a₂`. -/
theorem adj_left_unique {xs : List Nat} (hnd : xs.Nodup) {a₁ a₂ b : Nat}
    (h1 : Adj xs a₁ b) (h2 : Adj xs a₂ b) : a₁ = a₂ := by
  rcases h1 with ⟨l₁, r₁, rfl⟩
  rcases h2 with ⟨l₂, r₂, heq⟩
  have heq' : (l₁ ++ [a₁]) ++ b :: r₁ = (l₂ ++ [a₂]) ++ b :: r₂ := by
    simpa [List.append_assoc] using heq
  have hnd' : ((l₁ ++ [a₁]) ++ b :: r₁).Nodup := by simpa [List.append_assoc] using hnd
  obtain ⟨hl, _⟩ := append_cons_eq_unique hnd' heq'
  have hlast := congrArg (fun l => l.getLast?) hl
  simp at hlast
  exact hlast

/-- Exact case analysis on the predecessor of `b` in `bubblePass (h :: l₁ ++ x :: b :: l₂)`. -/
theorem bubblePass_adj_pred (h x b : Nat) (l₁ l₂ : List Nat) :
    let m := listMax h l₁
    (m > x ∧ m > b → Adj (bubblePass (h :: l₁ ++ x :: b :: l₂)) x b) ∧
    (m ≤ x ∧ x > b → Adj (bubblePass (h :: l₁ ++ x :: b :: l₂)) m b) := by
  intro m
  obtain ⟨out, heq, _⟩ := bubbleCarry_append h l₁ (x :: b :: l₂)
  have hbp : bubblePass (h :: l₁ ++ x :: b :: l₂) = out ++ bubbleCarry m (x :: b :: l₂) := by
    simpa [bubblePass, m] using heq
  constructor
  · rintro ⟨hmx, hmb⟩
    rw [hbp]
    simp only [bubbleCarry, hmx, hmb, ↓reduceIte]
    exact ⟨out, bubbleCarry m l₂, by simp⟩
  · rintro ⟨hmx, hxb⟩
    rw [hbp]
    have hnot : ¬ m > x := by omega
    simp only [bubbleCarry, hnot, hxb, ↓reduceIte]
    exact ⟨out, bubbleCarry x l₂, by simp⟩

/-- **Theorem 3 (`desBot_bubblePass_iff`):** Exact characterization of descent bottoms under
single-pass bubble sort: for any `Nodup` list `xs` and any `b`,
`IsDesBot (bubblePass xs) b ↔ IsDesBot xs b ∧ 2 ≤ leftInv xs b`. -/
theorem desBot_bubblePass_iff {xs : List Nat} (hnd : xs.Nodup) (b : Nat) :
    IsDesBot (bubblePass xs) b ↔ IsDesBot xs b ∧ 2 ≤ leftInv xs b := by
  have hnd_B : (bubblePass xs).Nodup := ((bubblePass_perm xs).nodup_iff).mpr hnd
  by_cases hb : b ∈ xs
  · obtain ⟨pref, suff, rfl⟩ := List.append_of_mem hb
    have hb_notin : b ∉ pref := by
      have hdisj := (List.nodup_append.mp hnd).2.2
      intro h'; exact hdisj b h' b List.mem_cons_self rfl
    cases pref with
    | nil =>
        have hli : leftInv ([] ++ b :: suff) b = 0 := by simp [leftInv]
        rw [hli]
        constructor
        · rintro ⟨a, hba, hadj⟩
          exfalso
          have hbef := before_of_adj hadj
          have hlt := bubbleCarry_before_lt b (List.nodup_cons.mp hnd).1 hbef
          omega
        · rintro ⟨_, h2⟩; omega
    | cons h pref' =>
        cases pref' with
        | nil =>
            have hli : leftInv ([h] ++ b :: suff) b ≤ 1 := by
              rw [leftInv_append_eq hb_notin]
              simp only [countGt]
              split <;> omega
            constructor
            · rintro ⟨a, hba, hadj⟩
              exfalso
              have hinv : IsInv (bubblePass ([h] ++ b :: suff)) a b := ⟨hba, before_of_adj hadj⟩
              rw [invSet_bubblePass_iff hnd] at hinv
              rcases hinv with ⟨⟨_, h1⟩, c, hac, ⟨hcb, h2⟩⟩
              have h2' := (leftInv_ge_two_iff_inv hnd (by simp)).mpr
                ⟨a, c, by omega, ⟨hba, h1⟩, ⟨hcb, h2⟩⟩
              omega
            · rintro ⟨_, h2⟩; omega
        | cons y pref'' =>
            have hne : y :: pref'' ≠ [] := by simp
            let x := (y :: pref'').getLast hne
            let mid := (y :: pref'').dropLast
            have hsplit : y :: pref'' = mid ++ [x] := list_eq_dropLast_append_getLast (y :: pref'') hne
            have hxs_eq : (h :: y :: pref'') ++ b :: suff = h :: mid ++ x :: b :: suff := by
              rw [hsplit]; simp [List.append_assoc]
            rw [hxs_eq] at hnd hnd_B ⊢
            let m := listMax h mid
            have hadj_xs : Adj (h :: mid ++ x :: b :: suff) x b := ⟨h :: mid, suff, by simp⟩
            have hdes_xs_iff : IsDesBot (h :: mid ++ x :: b :: suff) b ↔ b < x := by
              constructor
              · rintro ⟨a, hba, hadj⟩
                have ha : a = x := adj_left_unique hnd hadj hadj_xs
                rw [← ha]; exact hba
              · intro hbx; exact ⟨x, hbx, hadj_xs⟩
            have hli_eq : leftInv (h :: mid ++ x :: b :: suff) b =
                countGt b (h :: mid) + (if b < x then 1 else 0) := by
              have hb_not2 : b ∉ (h :: mid ++ [x]) := by
                have : h :: mid ++ [x] = h :: y :: pref'' := by
                  rw [hsplit]; simp
                rw [this]; exact hb_notin
              have heq2 : h :: mid ++ x :: b :: suff = (h :: mid ++ [x]) ++ b :: suff := by
                simp [List.append_assoc]
              rw [heq2, leftInv_append_eq hb_not2]
              suffices hcg : ∀ l : List Nat, countGt b (l ++ [x]) = countGt b l + (if b < x then 1 else 0) by
                simpa using hcg (h :: mid)
              intro l
              induction l with
              | nil => simp [countGt]
              | cons u us ihu => simp only [List.cons_append, countGt, ihu]; omega
            have hm_gt_iff : b < m ↔ 1 ≤ countGt b (h :: mid) := by
              rw [countGt_pos_iff]
              dsimp only [m]
              rw [listMax_gt_iff]
              constructor
              · rintro (hbh | ⟨c, hc, hbc⟩)
                · exact ⟨h, by simp, hbh⟩
                · exact ⟨c, by simp [hc], hbc⟩
              · rintro ⟨c, hc, hbc⟩
                simp only [List.mem_cons] at hc
                rcases hc with rfl | hc'
                · exact Or.inl hbc
                · exact Or.inr ⟨c, hc', hbc⟩
            have hpred := bubblePass_adj_pred h x b mid suff
            rw [hdes_xs_iff, hli_eq]
            by_cases hmx : m > x
            · by_cases hbx : b < x
              · have hmb : m > b := Nat.lt_trans hbx hmx
                have hadjB : Adj (bubblePass (h :: mid ++ x :: b :: suff)) x b :=
                  hpred.1 ⟨hmx, hmb⟩
                have hc1 : 1 ≤ countGt b (h :: mid) := hm_gt_iff.mp hmb
                constructor
                · intro _; exact ⟨hbx, by simp [hbx]; omega⟩
                · intro _; exact ⟨x, hbx, hadjB⟩
              · constructor
                · intro hdesB
                  exfalso
                  by_cases hmb : m > b
                  · have hadjB : Adj (bubblePass (h :: mid ++ x :: b :: suff)) x b :=
                      hpred.1 ⟨hmx, hmb⟩
                    rcases hdesB with ⟨a, hba, hadj⟩
                    have hax : a = x := adj_left_unique hnd_B hadj hadjB
                    rw [hax] at hba; exact hbx hba
                  · apply not_isDesBot_bubblePass_of_no_inv hnd _ hdesB
                    intro a ⟨hba, hbef⟩
                    have ha_in : a ∈ h :: mid ++ [x] := by
                      have hnd' : ((h :: mid ++ [x]) ++ b :: suff).Nodup := by
                        simpa [List.append_assoc] using hnd
                      rcases before_append_cases hnd' (by simpa [List.append_assoc] using hbef) with h1 | h2 | ⟨ha1, _⟩
                      · exact mem_of_before_left h1
                      · exfalso
                        have hnd2 : (b :: suff).Nodup := (List.nodup_append.mp hnd').2.1
                        rcases h2 with ⟨p₁, p₂, p₃, heq⟩
                        cases p₁ with
                        | nil => simp at heq; rcases heq with ⟨rfl, _⟩; omega
                        | cons z p₁' =>
                            simp at heq
                            have : b ∉ suff := (List.nodup_cons.mp hnd2).1
                            rw [heq.2] at this; exact this (by simp)
                      · exact ha1
                    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha_in
                    rcases ha_in with rfl | ha_mid | rfl
                    · have := le_listMax a mid; omega
                    · have := mem_le_listMax h ha_mid; omega
                    · omega
                · rintro ⟨hbx', _⟩; exact absurd hbx' hbx
            · by_cases hbx : b < x
              · have hadjB : Adj (bubblePass (h :: mid ++ x :: b :: suff)) m b :=
                  hpred.2 ⟨by omega, hbx⟩
                constructor
                · rintro ⟨a, hba, hadj⟩
                  have ham : a = m := adj_left_unique hnd_B hadj hadjB
                  rw [ham] at hba
                  have hc1 : 1 ≤ countGt b (h :: mid) := hm_gt_iff.mp hba
                  exact ⟨hbx, by simp [hbx]; omega⟩
                · rintro ⟨_, h2⟩
                  simp only [hbx, ↓reduceIte] at h2
                  have hbm : b < m := hm_gt_iff.mpr (by omega)
                  exact ⟨m, hbm, hadjB⟩
              · constructor
                · intro hdesB
                  exfalso
                  apply not_isDesBot_bubblePass_of_no_inv hnd _ hdesB
                  intro a ⟨hba, hbef⟩
                  have ha_in : a ∈ h :: mid ++ [x] := by
                    have hnd' : ((h :: mid ++ [x]) ++ b :: suff).Nodup := by
                      simpa [List.append_assoc] using hnd
                    rcases before_append_cases hnd' (by simpa [List.append_assoc] using hbef) with h1 | h2 | ⟨ha1, _⟩
                    · exact mem_of_before_left h1
                    · exfalso
                      have hnd2 : (b :: suff).Nodup := (List.nodup_append.mp hnd').2.1
                      rcases h2 with ⟨p₁, p₂, p₃, heq⟩
                      cases p₁ with
                      | nil => simp at heq; rcases heq with ⟨rfl, _⟩; omega
                      | cons z p₁' =>
                          simp at heq
                          have : b ∉ suff := (List.nodup_cons.mp hnd2).1
                          rw [heq.2] at this; exact this (by simp)
                    · exact ha1
                  simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha_in
                  rcases ha_in with rfl | ha_mid | rfl
                  · have := le_listMax a mid; omega
                  · have := mem_le_listMax h ha_mid; omega
                  · omega
                · rintro ⟨hbx', _⟩; exact absurd hbx' hbx
  · constructor
    · rintro ⟨a, _, hadj⟩
      exact absurd ((bubblePass_perm xs).mem_iff.mp (mem_of_before_right (before_of_adj hadj))) hb
    · rintro ⟨⟨a, _, hadj⟩, _⟩
      exact absurd (mem_of_before_right (before_of_adj hadj)) hb

/-- **Theorem 4 (`bubbleOrder_bubblePass_mono`):** Single-pass bubble sort is monotone in the
Bubble-Refined Order `BubbleLe` (`WeakBruhatLe ∧ DesBotSub`)! -/
theorem bubbleOrder_bubblePass_mono {xs ys : List Nat}
    (hperm : xs.Perm ys) (hnd_x : xs.Nodup) (hle : BubbleLe xs ys) :
    BubbleLe (bubblePass xs) (bubblePass ys) := by
  have hnd_y : ys.Nodup := (hperm.nodup_iff).mp hnd_x
  refine ⟨invSet_bubblePass_mono hnd_x hnd_y hle.1, ?_⟩
  intro b hb
  rw [desBot_bubblePass_iff hnd_x] at hb
  rw [desBot_bubblePass_iff hnd_y]
  have hb_in_x : b ∈ xs := by
    rcases hb.1 with ⟨a, _, hadj⟩
    exact mem_of_before_right (before_of_adj hadj)
  have hb_in_y : b ∈ ys := hperm.mem_iff.mp hb_in_x
  refine ⟨hle.2 b hb.1, ?_⟩
  rw [leftInv_ge_two_iff_inv hnd_x hb_in_x] at hb
  rw [leftInv_ge_two_iff_inv hnd_y hb_in_y]
  rcases hb.2 with ⟨c₁, c₂, hne, h1, h2⟩
  exact ⟨c₁, c₂, hne, hle.1 c₁ b h1, hle.1 c₂ b h2⟩

/-- Right-valley predicate: no element immediately following `b` is smaller than `b`. -/
def IsRightValley (xs : List Nat) (b : Nat) : Prop :=
  ∀ c, Adj xs b c → b < c

/-- Right-valley preservation under `bubblePass`: if `b` is a right-valley of `xs` and has at least
one left-inversion in `xs`, then `b` remains a right-valley of `bubblePass xs`. -/
theorem rightValley_bubblePass {xs : List Nat} (hnd : xs.Nodup) {b : Nat}
    (hrv : IsRightValley xs b) (hinv : ∃ a, IsInv xs a b) :
    IsRightValley (bubblePass xs) b := by
  have hnd_B : (bubblePass xs).Nodup := ((bubblePass_perm xs).nodup_iff).mpr hnd
  rcases hinv with ⟨a, hba, hbef⟩
  have hb_in : b ∈ xs := mem_of_before_right hbef
  obtain ⟨pref, suff, rfl⟩ := List.append_of_mem hb_in
  cases pref with
  | nil =>
      exfalso
      rcases hbef with ⟨l₁, l₂, l₃, heq⟩
      cases l₁ with
      | nil => simp at heq; rcases heq with ⟨rfl, _⟩; omega
      | cons z l₁' =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
          have : b ∉ suff := (List.nodup_cons.mp hnd).1
          rw [heq.2] at this; exact this (by simp)
  | cons h pref' =>
      obtain ⟨out, heq, _⟩ := bubbleCarry_append h pref' (b :: suff)
      have hbp : bubblePass ((h :: pref') ++ b :: suff) =
          out ++ bubbleCarry (listMax h pref') (b :: suff) := by
        simpa [bubblePass] using heq
      have hm_gt : b < listMax h pref' := by
        have ha_in : a ∈ h :: pref' := by
          rcases before_append_cases hnd hbef with h1 | h2 | ⟨ha1, _⟩
          · exact mem_of_before_left h1
          · exfalso
            have hnd2 : (b :: suff).Nodup := (List.nodup_append.mp hnd).2.1
            rcases h2 with ⟨p₁, p₂, p₃, heq2⟩
            cases p₁ with
            | nil => simp at heq2; rcases heq2 with ⟨rfl, _⟩; omega
            | cons z p₁' =>
                simp at heq2
                have : b ∉ suff := (List.nodup_cons.mp hnd2).1
                rw [heq2.2] at this; exact this (by simp)
          · exact ha1
        simp only [List.mem_cons] at ha_in
        rcases ha_in with rfl | ha'
        · exact Nat.lt_of_lt_of_le hba (le_listMax a pref')
        · exact Nat.lt_of_lt_of_le hba (mem_le_listMax h ha')
      rw [hbp] at hnd_B ⊢
      simp only [bubbleCarry, hm_gt, ↓reduceIte] at hnd_B ⊢
      intro c hadj
      cases suff with
      | nil =>
          simp only [bubbleCarry] at hadj hnd_B
          rcases hadj with ⟨q₁, q₂, hq⟩
          obtain ⟨_, hr⟩ := append_cons_eq_unique hnd_B hq
          simp only [List.cons.injEq] at hr
          rw [← hr.1]; exact hm_gt
      | cons d suff' =>
          have hbd : b < d := hrv d ⟨h :: pref', suff', by simp⟩
          simp only [bubbleCarry] at hadj hnd_B
          by_cases hmd : listMax h pref' > d
          · simp only [hmd, ↓reduceIte] at hadj hnd_B
            rcases hadj with ⟨q₁, q₂, hq⟩
            obtain ⟨_, hr⟩ := append_cons_eq_unique hnd_B hq
            simp only [List.cons.injEq] at hr
            rw [← hr.1]; exact hbd
          · simp only [hmd, ↓reduceIte] at hadj hnd_B
            rcases hadj with ⟨q₁, q₂, hq⟩
            obtain ⟨_, hr⟩ := append_cons_eq_unique hnd_B hq
            simp only [List.cons.injEq] at hr
            rw [← hr.1]; exact hm_gt

end BubbleDesBot

end WeakBruhatCommutators
