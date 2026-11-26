/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakBruhatCommutators.Defs

/-!
# Basic Order, Inversion-Set, and Descent-Bottom Lemmas

Pure-`Init` foundation for `Before`, `Adj`, `IsInv`, `IsDesBot`, `leftInv`, `invCnt`, and `desCnt`
on duplicate-free lists (`List.Nodup`). Includes the pure inversion-set characterization of descent
bottoms (`isDesBot_iff_invSet`) and cardinality dominance from set inclusions
(`invCnt_le_of_weakBruhatLe`, `desCnt_le_of_desBotSub`).
-/

namespace WeakBruhatCommutators

section ListSplitting

theorem mem_of_before_left {xs : List Nat} {a b : Nat} (h : Before xs a b) : a ∈ xs := by
  rcases h with ⟨l₁, l₂, l₃, rfl⟩
  simp

theorem mem_of_before_right {xs : List Nat} {a b : Nat} (h : Before xs a b) : b ∈ xs := by
  rcases h with ⟨l₁, l₂, l₃, rfl⟩
  simp

theorem list_eq_dropLast_append_getLast : ∀ (l : List Nat) (h : l ≠ []),
    l = l.dropLast ++ [l.getLast h]
  | [], h => absurd rfl h
  | [_], _ => rfl
  | x :: y :: rest, _ => by
      have ih := list_eq_dropLast_append_getLast (y :: rest) (by simp)
      simp only [List.dropLast, List.getLast, List.cons_append]
      exact congrArg (x :: ·) ih

theorem before_of_adj {xs : List Nat} {a b : Nat} (h : Adj xs a b) : Before xs a b := by
  rcases h with ⟨l₁, l₂, rfl⟩
  exact ⟨l₁, [], l₂, by simp⟩

theorem before_irrefl {xs : List Nat} (hnd : xs.Nodup) {a : Nat} : ¬ Before xs a a := by
  rintro ⟨l₁, l₂, l₃, rfl⟩
  have hnd' : (l₁ ++ (a :: l₂ ++ a :: l₃)).Nodup := by simpa [List.append_assoc] using hnd
  have h1 : (a :: l₂ ++ a :: l₃).Nodup := (List.nodup_append.mp hnd').2.1
  have h2 : a ∉ l₂ ++ a :: l₃ := (List.nodup_cons.mp h1).1
  exact h2 (by simp)

/-- On a `Nodup` list, splitting at `x` is unique. -/
theorem append_cons_eq_unique {l₁ l₂ r₁ r₂ : List Nat} {x : Nat}
    (hnd : (l₁ ++ x :: r₁).Nodup) (heq : l₁ ++ x :: r₁ = l₂ ++ x :: r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at heq
          exact ⟨rfl, heq.2⟩
      | cons y l₂' =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
          rcases heq with ⟨rfl, htail⟩
          have hx : x ∉ r₁ := (List.nodup_cons.mp hnd).1
          rw [htail] at hx
          exact absurd (by simp) hx
  | cons a l₁' ih =>
      cases l₂ with
      | nil =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
          rcases heq with ⟨rfl, _⟩
          have ha : a ∉ l₁' ++ a :: r₁ := (List.nodup_cons.mp hnd).1
          exact absurd (by simp) ha
      | cons b l₂' =>
          simp only [List.cons_append, List.cons.injEq] at heq
          rcases heq with ⟨rfl, htail⟩
          have hnd' : (l₁' ++ x :: r₁).Nodup := (List.nodup_cons.mp hnd).2
          obtain ⟨h1, h2⟩ := ih hnd' htail
          exact ⟨congrArg (a :: ·) h1, h2⟩

theorem before_asymm {xs : List Nat} (hnd : xs.Nodup) {a b : Nat}
    (h1 : Before xs a b) (h2 : Before xs b a) : False := by
  rcases h1 with ⟨l₁, l₂, l₃, rfl⟩
  rcases h2 with ⟨r₁, r₂, r₃, heq⟩
  have h1' : (l₁ ++ a :: (l₂ ++ b :: l₃)) = (r₁ ++ b :: r₂) ++ a :: r₃ := by
    simpa [List.append_assoc] using heq
  have hnd' : (l₁ ++ a :: (l₂ ++ b :: l₃)).Nodup := by simpa [List.append_assoc] using hnd
  obtain ⟨hl, hr⟩ := append_cons_eq_unique hnd' h1'
  have hb_in_l1 : b ∈ l₁ := by rw [hl]; simp
  have hb_in_r : b ∈ l₂ ++ b :: l₃ := by simp
  have hdisj := (List.nodup_append.mp hnd').2.2
  exact hdisj b hb_in_l1 b (List.mem_cons_of_mem a hb_in_r) rfl

theorem before_trans {xs : List Nat} (hnd : xs.Nodup) {a b c : Nat}
    (h1 : Before xs a b) (h2 : Before xs b c) : Before xs a c := by
  rcases h1 with ⟨l₁, l₂, l₃, rfl⟩
  rcases h2 with ⟨r₁, r₂, r₃, heq⟩
  have h1' : (l₁ ++ a :: l₂) ++ b :: l₃ = r₁ ++ b :: (r₂ ++ c :: r₃) := by
    simpa [List.append_assoc] using heq
  have hnd' : ((l₁ ++ a :: l₂) ++ b :: l₃).Nodup := by simpa [List.append_assoc] using hnd
  obtain ⟨_, hr⟩ := append_cons_eq_unique hnd' h1'
  refine ⟨l₁, l₂ ++ b :: r₂, r₃, ?_⟩
  rw [hr]
  simp [List.append_assoc]

theorem before_or_before {xs : List Nat} {a b : Nat}
    (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) : Before xs a b ∨ Before xs b a := by
  induction xs with
  | nil => simp at ha
  | cons x rest ih =>
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha'
      · rcases hb with rfl | hb'
        · exact absurd rfl hne
        · obtain ⟨l₂, l₃, rfl⟩ := List.append_of_mem hb'
          exact Or.inl ⟨[], l₂, l₃, by simp⟩
      · rcases hb with rfl | hb'
        · obtain ⟨l₂, l₃, rfl⟩ := List.append_of_mem ha'
          exact Or.inr ⟨[], l₂, l₃, by simp⟩
        · rcases ih ha' hb' with ⟨l₁, l₂, l₃, rfl⟩ | ⟨l₁, l₂, l₃, rfl⟩
          · exact Or.inl ⟨x :: l₁, l₂, l₃, by simp⟩
          · exact Or.inr ⟨x :: l₁, l₂, l₃, by simp⟩

theorem before_cons_iff {x a b : Nat} {xs : List Nat} (hnd : (x :: xs).Nodup) :
    Before (x :: xs) a b ↔ (a = x ∧ b ∈ xs) ∨ Before xs a b := by
  constructor
  · rintro ⟨l₁, l₂, l₃, heq⟩
    cases l₁ with
    | nil =>
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact Or.inl ⟨rfl, by simp⟩
    | cons y l₁' =>
        simp only [List.cons_append, List.cons.injEq] at heq
        exact Or.inr ⟨l₁', l₂, l₃, heq.2⟩
  · rintro (⟨rfl, hb⟩ | ⟨l₁, l₂, l₃, rfl⟩)
    · obtain ⟨l₂, l₃, rfl⟩ := List.append_of_mem hb
      exact ⟨[], l₂, l₃, by simp⟩
    · exact ⟨x :: l₁, l₂, l₃, by simp⟩

theorem before_append_of_mem {l₁ l₂ : List Nat} {a b : Nat} (ha : a ∈ l₁) (hb : b ∈ l₂) :
    Before (l₁ ++ l₂) a b := by
  obtain ⟨p₁, p₂, rfl⟩ := List.append_of_mem ha
  obtain ⟨q₁, q₂, rfl⟩ := List.append_of_mem hb
  exact ⟨p₁, p₂ ++ q₁, q₂, by simp [List.append_assoc]⟩

theorem before_append_left {l₁ l₂ : List Nat} {a b : Nat} (h : Before l₁ a b) :
    Before (l₁ ++ l₂) a b := by
  rcases h with ⟨p₁, p₂, p₃, rfl⟩
  exact ⟨p₁, p₂, p₃ ++ l₂, by simp [List.append_assoc]⟩

theorem before_append_right {l₁ l₂ : List Nat} {a b : Nat} (h : Before l₂ a b) :
    Before (l₁ ++ l₂) a b := by
  rcases h with ⟨p₁, p₂, p₃, rfl⟩
  exact ⟨l₁ ++ p₁, p₂, p₃, by simp [List.append_assoc]⟩

/-- On a `Nodup` list, if `Before (l₁ ++ l₂) a b`, then either `a, b` are in `l₁`, or in `l₂`,
or `a ∈ l₁ ∧ b ∈ l₂`. -/
theorem before_append_cases {l₁ l₂ : List Nat} (hnd : (l₁ ++ l₂).Nodup) {a b : Nat}
    (h : Before (l₁ ++ l₂) a b) :
    Before l₁ a b ∨ Before l₂ a b ∨ (a ∈ l₁ ∧ b ∈ l₂) := by
  have ha : a ∈ l₁ ++ l₂ := mem_of_before_left h
  have hb : b ∈ l₁ ++ l₂ := mem_of_before_right h
  have hne : a ≠ b := fun heq => before_irrefl hnd (heq ▸ h)
  simp only [List.mem_append] at ha hb
  rcases ha with ha1 | ha2 <;> rcases hb with hb1 | hb2
  · rcases before_or_before ha1 hb1 hne with h1 | h2
    · exact Or.inl h1
    · exact absurd (before_append_left h2) (fun h' => before_asymm hnd h h')
  · exact Or.inr (Or.inr ⟨ha1, hb2⟩)
  · exact absurd (before_append_of_mem hb1 ha2) (fun h' => before_asymm hnd h h')
  · rcases before_or_before ha2 hb2 hne with h1 | h2
    · exact Or.inr (Or.inl h1)
    · exact absurd (before_append_right h2) (fun h' => before_asymm hnd h h')

/-- On a `Nodup` list, `a` is adjacent before `b` iff `Before xs a b` and nothing lies between them. -/
theorem adj_iff_before_no_between {xs : List Nat} (hnd : xs.Nodup) {a b : Nat} :
    Adj xs a b ↔ Before xs a b ∧ ∀ c, ¬ (Before xs a c ∧ Before xs c b) := by
  constructor
  · rintro ⟨l₁, l₂, rfl⟩
    refine ⟨⟨l₁, [], l₂, by simp⟩, ?_⟩
    rintro c ⟨h1, h2⟩
    rcases h1 with ⟨p₁, p₂, p₃, heq1⟩
    have h1' : l₁ ++ a :: (b :: l₂) = p₁ ++ a :: (p₂ ++ c :: p₃) := by
      simpa [List.append_assoc] using heq1
    have hnd' : (l₁ ++ a :: (b :: l₂)).Nodup := by simpa [List.append_assoc] using hnd
    obtain ⟨_, hr1⟩ := append_cons_eq_unique hnd' h1'
    have hc_in : c ∈ b :: l₂ := by rw [hr1]; simp
    simp only [List.mem_cons] at hc_in
    rcases hc_in with rfl | hc_in_l2
    · exact before_irrefl hnd h2
    · have hbc : Before (l₁ ++ a :: b :: l₂) b c := by
        obtain ⟨q₁, q₂, rfl⟩ := List.append_of_mem hc_in_l2
        exact ⟨l₁ ++ [a], q₁, q₂, by simp [List.append_assoc]⟩
      exact before_asymm hnd h2 hbc
  · rintro ⟨⟨l₁, l₂, l₃, rfl⟩, hno⟩
    cases l₂ with
    | nil => exact ⟨l₁, l₃, by simp⟩
    | cons c l₂' =>
        exfalso
        apply hno c
        refine ⟨⟨l₁, [], l₂' ++ b :: l₃, by simp [List.append_assoc]⟩,
                ⟨l₁ ++ [a], l₂', l₃, by simp [List.append_assoc]⟩⟩

end ListSplitting

section PureInvSetDesBot

/-- **Pure inversion-set characterization of descent bottoms:**
On any `Nodup` list `xs`, `b` is a descent bottom of `xs` if and only if there exists `a > b`
inverted with `b` such that no `z < b` lies between `a` and `b` (stated purely via `IsInv`). -/
theorem isDesBot_iff_invSet {xs : List Nat} (hnd : xs.Nodup) {b : Nat} :
    IsDesBot xs b ↔
      ∃ a, IsInv xs a b ∧ ∀ z, z < b → IsInv xs a z → IsInv xs b z := by
  constructor
  · rintro ⟨a, hba, hadj⟩
    refine ⟨a, ⟨hba, before_of_adj hadj⟩, ?_⟩
    intro z hzb ⟨_, haz⟩
    refine ⟨hzb, ?_⟩
    have hz_mem : z ∈ xs := mem_of_before_right haz
    have hb_mem : b ∈ xs := mem_of_before_right (before_of_adj hadj)
    rcases before_or_before hb_mem hz_mem (by omega) with hbz | hzb'
    · exact hbz
    · exfalso
      exact ((adj_iff_before_no_between hnd).mp hadj).2 z ⟨haz, hzb'⟩
  · rintro ⟨a, ⟨hba, hab⟩, hno⟩
    rcases hab with ⟨l₁, l₂, l₃, rfl⟩
    -- Look at the last element of `a :: l₂`: it is adjacent before `b`!
    have hne : a :: l₂ ≠ [] := by simp
    let prev := (a :: l₂).getLast hne
    have hsplit : a :: l₂ = (a :: l₂).dropLast ++ [prev] :=
      list_eq_dropLast_append_getLast (a :: l₂) hne
    have hadj : Adj (l₁ ++ a :: l₂ ++ b :: l₃) prev b := by
      refine ⟨l₁ ++ (a :: l₂).dropLast, l₃, ?_⟩
      have : l₁ ++ a :: l₂ ++ b :: l₃ = l₁ ++ ((a :: l₂).dropLast ++ [prev]) ++ b :: l₃ := by
        rw [← hsplit]
      simpa [List.append_assoc] using this
    have hprev_gt : b < prev := by
      have hmem : prev ∈ a :: l₂ := List.getLast_mem hne
      simp only [List.mem_cons] at hmem
      rcases hmem with hpa | hpl2
      · rw [hpa]; exact hba
      · have hne_b : prev ≠ b := by
          intro heq
          subst heq
          have hnd' : ((l₁ ++ a :: l₂) ++ prev :: l₃).Nodup := by
            simpa [List.append_assoc] using hnd
          have hdisj := (List.nodup_append.mp hnd').2.2
          exact hdisj prev (List.mem_append_right l₁ (List.mem_cons_of_mem a hpl2)) prev List.mem_cons_self rfl
        by_cases hlt : prev < b
        · obtain ⟨q₁, q₂, hq⟩ := List.append_of_mem hpl2
          have haz : IsInv (l₁ ++ a :: l₂ ++ b :: l₃) a prev := by
            refine ⟨by omega, ⟨l₁, q₁, q₂ ++ b :: l₃, ?_⟩⟩
            rw [hq]; simp [List.append_assoc]
          have hbz : IsInv (l₁ ++ a :: l₂ ++ b :: l₃) b prev := hno prev hlt haz
          exact absurd hbz.2 (fun h => before_asymm hnd (before_of_adj hadj) h)
        · omega
    exact ⟨prev, hprev_gt, hadj⟩

end PureInvSetDesBot

section CountingBridges

theorem leftInv_append_eq {l₁ l₂ : List Nat} {b : Nat} (hb : b ∉ l₁) :
    leftInv (l₁ ++ b :: l₂) b = countGt b l₁ := by
  induction l₁ with
  | nil => simp [leftInv, countGt]
  | cons x xs ih =>
      have hxb : x ≠ b := fun h => hb (by simp [h])
      have hb' : b ∉ xs := fun h => hb (by simp [h])
      simp only [List.cons_append, leftInv, hxb, ↓reduceIte, countGt, ih hb']

theorem countGt_pos_iff {b : Nat} : ∀ {xs : List Nat},
    1 ≤ countGt b xs ↔ ∃ c, c ∈ xs ∧ b < c
  | [] => by simp [countGt]
  | x :: xs => by
      simp only [countGt, List.mem_cons]
      by_cases h : b < x
      · simp [h]
      · simp only [h, ↓reduceIte, Nat.zero_add, countGt_pos_iff]
        constructor
        · rintro ⟨c, hc, hbc⟩; exact ⟨c, Or.inr hc, hbc⟩
        · rintro ⟨c, rfl | hc, hbc⟩
          · exact absurd hbc h
          · exact ⟨c, hc, hbc⟩

theorem countGt_ge_two_iff {b : Nat} : ∀ {xs : List Nat}, xs.Nodup →
    (2 ≤ countGt b xs ↔ ∃ c₁ c₂, c₁ ∈ xs ∧ c₂ ∈ xs ∧ c₁ ≠ c₂ ∧ b < c₁ ∧ b < c₂)
  | [], _ => by simp [countGt]
  | x :: xs, hnd => by
      have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
      have hx_notin : x ∉ xs := (List.nodup_cons.mp hnd).1
      simp only [countGt]
      by_cases hbx : b < x
      · simp only [hbx, ↓reduceIte]
        constructor
        · intro h2
          have h1 : 1 ≤ countGt b xs := by omega
          obtain ⟨c₂, hc₂, hbc₂⟩ := countGt_pos_iff.mp h1
          exact ⟨x, c₂, by simp, by simp [hc₂], fun heq => hx_notin (heq ▸ hc₂), hbx, hbc₂⟩
        · rintro ⟨c₁, c₂, hc₁, hc₂, hne, hbc₁, hbc₂⟩
          simp only [List.mem_cons] at hc₁ hc₂
          rcases hc₁ with rfl | hc₁'
          · rcases hc₂ with rfl | hc₂'
            · exact absurd rfl hne
            · have := countGt_pos_iff.mpr ⟨c₂, hc₂', hbc₂⟩; omega
          · have := countGt_pos_iff.mpr ⟨c₁, hc₁', hbc₁⟩; omega
      · simp only [hbx, ↓reduceIte, Nat.zero_add, countGt_ge_two_iff hnd']
        constructor
        · rintro ⟨c₁, c₂, hc₁, hc₂, hne, hbc₁, hbc₂⟩
          exact ⟨c₁, c₂, by simp [hc₁], by simp [hc₂], hne, hbc₁, hbc₂⟩
        · rintro ⟨c₁, c₂, hc₁, hc₂, hne, hbc₁, hbc₂⟩
          simp only [List.mem_cons] at hc₁ hc₂
          rcases hc₁ with rfl | hc₁'
          · exact absurd hbc₁ hbx
          · rcases hc₂ with rfl | hc₂'
            · exact absurd hbc₂ hbx
            · exact ⟨c₁, c₂, hc₁', hc₂', hne, hbc₁, hbc₂⟩

/-- `2 ≤ leftInv xs b` iff there exist two distinct elements `c₁ ≠ c₂` both inverted with `b`. -/
theorem leftInv_ge_two_iff_inv {xs : List Nat} (hnd : xs.Nodup) {b : Nat} (hb : b ∈ xs) :
    2 ≤ leftInv xs b ↔ ∃ c₁ c₂, c₁ ≠ c₂ ∧ IsInv xs c₁ b ∧ IsInv xs c₂ b := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hb
  have hb_notin : b ∉ l₁ := by
    have hdisj := (List.nodup_append.mp hnd).2.2
    intro h; exact hdisj b h b List.mem_cons_self rfl
  have hnd₁ : l₁.Nodup := (List.nodup_append.mp hnd).1
  rw [leftInv_append_eq hb_notin, countGt_ge_two_iff hnd₁]
  constructor
  · rintro ⟨c₁, c₂, hc₁, hc₂, hne, hbc₁, hbc₂⟩
    refine ⟨c₁, c₂, hne, ⟨hbc₁, before_append_of_mem hc₁ (by simp)⟩,
            ⟨hbc₂, before_append_of_mem hc₂ (by simp)⟩⟩
  · rintro ⟨c₁, c₂, hne, ⟨hbc₁, h1⟩, ⟨hbc₂, h2⟩⟩
    have hc₁ : c₁ ∈ l₁ := by
      rcases before_append_cases hnd h1 with hb1 | hb2 | ⟨hc, _⟩
      · exact absurd (mem_of_before_right hb1) hb_notin
      · exfalso
        rcases hb2 with ⟨p₁, p₂, p₃, heq⟩
        have hnd2 : (b :: l₂).Nodup := (List.nodup_append.mp hnd).2.1
        cases p₁ with
        | nil =>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
            rcases heq with ⟨rfl, _⟩; omega
        | cons y p₁' =>
            simp only [List.cons_append, List.cons.injEq] at heq
            rcases heq with ⟨rfl, htail⟩
            have : b ∉ l₂ := (List.nodup_cons.mp hnd2).1
            rw [htail] at this; exact this (by simp)
      · exact hc
    have hc₂ : c₂ ∈ l₁ := by
      rcases before_append_cases hnd h2 with hb1 | hb2 | ⟨hc, _⟩
      · exact absurd (mem_of_before_right hb1) hb_notin
      · exfalso
        rcases hb2 with ⟨p₁, p₂, p₃, heq⟩
        have hnd2 : (b :: l₂).Nodup := (List.nodup_append.mp hnd).2.1
        cases p₁ with
        | nil =>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
            rcases heq with ⟨rfl, _⟩; omega
        | cons y p₁' =>
            simp only [List.cons_append, List.cons.injEq] at heq
            rcases heq with ⟨rfl, htail⟩
            have : b ∉ l₂ := (List.nodup_cons.mp hnd2).1
            rw [htail] at this; exact this (by simp)
      · exact hc
    exact ⟨c₁, c₂, hc₁, hc₂, hne, hbc₁, hbc₂⟩

/-- Count elements of `l` satisfying a decidable predicate `P`. -/
private def countPred (P : Nat → Bool) : List Nat → Nat
  | [] => 0
  | x :: xs => (if P x then 1 else 0) + countPred P xs

private theorem countPred_perm {P : Nat → Bool} {xs ys : List Nat} (h : xs.Perm ys) :
    countPred P xs = countPred P ys := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [countPred, ih]
  | swap a b l => simp only [countPred]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem countPred_mono {P Q : Nat → Bool} (h : ∀ x, P x = true → Q x = true) :
    ∀ xs : List Nat, countPred P xs ≤ countPred Q xs
  | [] => Nat.le_refl 0
  | x :: xs => by
      simp only [countPred]
      have hih := countPred_mono h xs
      cases hPx : P x
      · simp; omega
      · rw [h x hPx]; simp; omega

/-- Helper: count how many `b` in `ys` satisfy `IsInv xs a b` when `xs` is `Nodup`. -/
private def isBeforeBool (xs : List Nat) (a b : Nat) : Bool :=
  match xs with
  | [] => false
  | x :: rest => if x = a then rest.contains b else isBeforeBool rest a b

private theorem isBeforeBool_eq_true_iff {xs : List Nat} (hnd : xs.Nodup) {a b : Nat} :
    isBeforeBool xs a b = true ↔ Before xs a b := by
  induction xs with
  | nil => simp [isBeforeBool, Before]
  | cons x rest ih =>
      have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hx : x ∉ rest := (List.nodup_cons.mp hnd).1
      rw [before_cons_iff hnd]
      simp only [isBeforeBool]
      by_cases hxa : x = a
      · subst hxa
        simp only [↓reduceIte, List.contains_eq_mem, decide_eq_true_eq]
        constructor
        · intro hb; exact Or.inl ⟨trivial, hb⟩
        · rintro (⟨_, hb⟩ | hbef)
          · exact hb
          · exact absurd (mem_of_before_left hbef) hx
      · simp only [hxa, ↓reduceIte, ih hnd']
        constructor
        · intro h; exact Or.inr h
        · rintro (⟨rfl, _⟩ | h)
          · exact absurd rfl hxa
          · exact h

private def isInvBool (xs : List Nat) (a b : Nat) : Bool :=
  decide (b < a) && isBeforeBool xs a b

private theorem isInvBool_eq_true_iff {xs : List Nat} (hnd : xs.Nodup) {a b : Nat} :
    isInvBool xs a b = true ↔ IsInv xs a b := by
  simp only [isInvBool, Bool.and_eq_true, decide_eq_true_eq, isBeforeBool_eq_true_iff hnd, IsInv]

/-- Sum of `countPred (isInvBool xs a) ys` over all `a ∈ l`. -/
private def sumInvBool (xs : List Nat) (ys : List Nat) : List Nat → Nat
  | [] => 0
  | a :: rest => countPred (isInvBool xs a) ys + sumInvBool xs ys rest

private theorem sumInvBool_perm_left {xs ys l₁ l₂ : List Nat} (h : l₁.Perm l₂) :
    sumInvBool xs ys l₁ = sumInvBool xs ys l₂ := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [sumInvBool, ih]
  | swap a b l => simp only [sumInvBool]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem countPred_isInvBool_cons_self {a : Nat} {xs : List Nat} (hnd : (a :: xs).Nodup) :
    countPred (isInvBool (a :: xs) a) (a :: xs) = countLt a xs := by
  have h1 : isInvBool (a :: xs) a a = false := by
    simp [isInvBool]
  simp only [countPred, h1, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  have ha_notin : a ∉ xs := (List.nodup_cons.mp hnd).1
  suffices hgen : ∀ l : List Nat, (∀ b ∈ l, b ∈ xs) →
      countPred (isInvBool (a :: xs) a) l = countLt a l by
    exact hgen xs (fun _ h => h)
  intro l hl
  induction l with
  | nil => rfl
  | cons b l' ih =>
      have hb_in : b ∈ xs := hl b (by simp)
      have hbef : isBeforeBool (a :: xs) a b = true := by
        simp [isBeforeBool, List.contains_eq_mem, hb_in]
      simp only [countPred, isInvBool, hbef, Bool.and_true, decide_eq_true_eq, countLt]
      rw [ih (fun c hc => hl c (by simp [hc]))]

private theorem sumInvBool_eq_invCnt : ∀ xs : List Nat, xs.Nodup →
    sumInvBool xs xs xs = invCnt xs
  | [], _ => rfl
  | a :: rest, hnd => by
      have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
      have ha_notin : a ∉ rest := (List.nodup_cons.mp hnd).1
      simp only [sumInvBool, invCnt, countPred_isInvBool_cons_self hnd]
      congr 1
      suffices htail : ∀ l : List Nat, (∀ x ∈ l, x ∈ rest) →
          sumInvBool (a :: rest) (a :: rest) l = sumInvBool rest rest l by
        rw [htail rest (fun _ h => h), sumInvBool_eq_invCnt rest hnd']
      intro l hl
      induction l with
      | nil => rfl
      | cons x l' ih =>
          have hx_in : x ∈ rest := hl x (by simp)
          have hax : a ≠ x := fun h => ha_notin (h ▸ hx_in)
          simp only [sumInvBool, ih (fun y hy => hl y (by simp [hy]))]
          congr 1
          have hxa : isInvBool (a :: rest) x a = false := by
            simp only [isInvBool, isBeforeBool, hax, ↓reduceIte]
            by_cases h : isBeforeBool rest x a = true
            · exfalso
              exact ha_notin (mem_of_before_right ((isBeforeBool_eq_true_iff hnd').mp h))
            · simp [Bool.eq_false_iff.mpr h]
          simp only [countPred, hxa, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
          suffices hcp : ∀ r : List Nat, countPred (isInvBool (a :: rest) x) r =
              countPred (isInvBool rest x) r from hcp rest
          intro r
          induction r with
          | nil => rfl
          | cons y r' ihr =>
              rw [countPred, countPred, ihr]
              simp only [isInvBool, isBeforeBool, hax, ↓reduceIte]
              rfl

/-- **Inversion-count dominance from Right Weak Bruhat Order:**
If `xs.Perm ys`, `xs.Nodup`, and `WeakBruhatLe xs ys`, then `invCnt xs ≤ invCnt ys`. -/
theorem invCnt_le_of_weakBruhatLe {xs ys : List Nat}
    (hperm : xs.Perm ys) (hnd : xs.Nodup) (hle : WeakBruhatLe xs ys) :
    invCnt xs ≤ invCnt ys := by
  have hnd_y : ys.Nodup := (hperm.nodup_iff).mp hnd
  rw [← sumInvBool_eq_invCnt xs hnd, ← sumInvBool_eq_invCnt ys hnd_y]
  rw [sumInvBool_perm_left hperm]
  suffices hgen : ∀ l : List Nat, sumInvBool xs xs l ≤ sumInvBool ys ys l from hgen ys
  intro l
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a l' ih =>
      simp only [sumInvBool]
      rw [countPred_perm hperm]
      have h1 : countPred (isInvBool xs a) ys ≤ countPred (isInvBool ys a) ys := by
        apply countPred_mono
        intro b hb
        exact (isInvBool_eq_true_iff hnd_y).mpr (hle a b ((isInvBool_eq_true_iff hnd).mp hb))
      omega

/-- Boolean test for `IsDesBot xs b`. -/
private def isDesBotBool : List Nat → Nat → Bool
  | [], _ => false
  | [_], _ => false
  | x :: y :: rest, b => (decide (b < x) && decide (y = b)) || isDesBotBool (y :: rest) b

private theorem isDesBotBool_eq_true_iff (xs : List Nat) (b : Nat) :
    isDesBotBool xs b = true ↔ IsDesBot xs b := by
  induction xs with
  | nil =>
      simp only [isDesBotBool, Bool.false_eq_true, false_iff]
      rintro ⟨a, _, l₁, l₂, heq⟩; cases l₁ <;> simp at heq
  | cons x rest ih =>
      cases rest with
      | nil =>
          simp only [isDesBotBool, Bool.false_eq_true, false_iff]
          rintro ⟨a, _, l₁, l₂, heq⟩; cases l₁ <;> simp at heq
      | cons y r =>
          simp only [isDesBotBool, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih]
          constructor
          · rintro (⟨hbx, rfl⟩ | ⟨a, hba, l₁, l₂, heq⟩)
            · exact ⟨x, hbx, [], r, rfl⟩
            · exact ⟨a, hba, x :: l₁, l₂, by simp [heq]⟩
          · rintro ⟨a, hba, l₁, l₂, heq⟩
            cases l₁ with
            | nil =>
                simp only [List.nil_append, List.cons.injEq] at heq
                rcases heq with ⟨rfl, rfl, _⟩
                exact Or.inl ⟨hba, rfl⟩
            | cons z l₁' =>
                simp only [List.cons_append, List.cons.injEq] at heq
                exact Or.inr ⟨a, hba, l₁', l₂, heq.2⟩

private theorem countPred_isDesBotBool_eq_desCnt : ∀ xs : List Nat, xs.Nodup →
    countPred (isDesBotBool xs) xs = desCnt xs
  | [], _ => rfl
  | [x], _ => by simp [countPred, isDesBotBool, desCnt]
  | x :: y :: rest, hnd => by
      have hnd_tail : (y :: rest).Nodup := (List.nodup_cons.mp hnd).2
      have hx_notin : x ∉ y :: rest := (List.nodup_cons.mp hnd).1
      have hx_false : isDesBotBool (x :: y :: rest) x = false := by
        cases h : isDesBotBool (x :: y :: rest) x
        · rfl
        · exfalso
          obtain ⟨a, hax, l₁, l₂, heq⟩ := (isDesBotBool_eq_true_iff _ _).mp h
          cases l₁ with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at heq
              rcases heq with ⟨rfl, rfl, _⟩; omega
          | cons z l₁' =>
              simp only [List.cons_append, List.cons.injEq] at heq
              have : x ∈ y :: rest := by rw [heq.2]; simp
              exact hx_notin this
      rw [countPred, hx_false]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, desCnt]
      have hy_notin : y ∉ rest := (List.nodup_cons.mp hnd_tail).1
      have hy_tail_false : isDesBotBool (y :: rest) y = false := by
        cases h : isDesBotBool (y :: rest) y
        · rfl
        · exfalso
          obtain ⟨a, hay, l₁, l₂, heq⟩ := (isDesBotBool_eq_true_iff _ _).mp h
          cases l₁ with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at heq
              rcases heq with ⟨rfl, rfl, _⟩; omega
          | cons z l₁' =>
              simp only [List.cons_append, List.cons.injEq] at heq
              have : y ∈ rest := by rw [heq.2]; simp
              exact hy_notin this
      have htail_eq : countPred (isDesBotBool (x :: y :: rest)) (y :: rest) =
          (if x > y then 1 else 0) + countPred (isDesBotBool (y :: rest)) (y :: rest) := by
        have hy_val : isDesBotBool (x :: y :: rest) y = decide (y < x) := by
          simp [isDesBotBool, hy_tail_false]
        rw [countPred, countPred, hy_tail_false, hy_val]
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        have hrest_eq : ∀ l : List Nat, (∀ b ∈ l, b ≠ y) →
            countPred (isDesBotBool (x :: y :: rest)) l = countPred (isDesBotBool (y :: rest)) l := by
          intro l hl
          induction l with
          | nil => rfl
          | cons b l' ihl =>
              have hby : y ≠ b := Ne.symm (hl b (by simp))
              rw [countPred, countPred, ihl (fun c hc => hl c (by simp [hc]))]
              simp only [isDesBotBool, hby, decide_false, Bool.and_false, Bool.false_or]
        rw [hrest_eq rest (fun b hb heq => hy_notin (heq ▸ hb))]
        by_cases hxy : x > y <;> simp [hxy]
      rw [htail_eq, countPred_isDesBotBool_eq_desCnt (y :: rest) hnd_tail]

/-- **Descent-count dominance from descent-bottom set inclusion:**
If `xs.Perm ys`, `xs.Nodup`, and `DesBotSub xs ys`, then `desCnt xs ≤ desCnt ys`. -/
theorem desCnt_le_of_desBotSub {xs ys : List Nat}
    (hperm : xs.Perm ys) (hnd : xs.Nodup) (hsub : DesBotSub xs ys) :
    desCnt xs ≤ desCnt ys := by
  have hnd_y : ys.Nodup := (hperm.nodup_iff).mp hnd
  rw [← countPred_isDesBotBool_eq_desCnt xs hnd, ← countPred_isDesBotBool_eq_desCnt ys hnd_y]
  rw [countPred_perm hperm]
  apply countPred_mono
  intro b hb
  exact (isDesBotBool_eq_true_iff ys b).mpr (hsub b ((isDesBotBool_eq_true_iff xs b).mp hb))

end CountingBridges

end WeakBruhatCommutators
