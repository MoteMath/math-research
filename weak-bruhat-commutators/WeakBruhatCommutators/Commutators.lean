/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakBruhatCommutators.WestPop

/-!
# Weak-Bruhat and Descent-Bottom Commutators for Bubble, West, and Pop-Stack Sorting

Proves the complete Weak-Bruhat (`≤_R`) and Bubble-Refined (`⪯_B = ≤_R ∧ DesBotSub`) commutator
and sandwich theory for single/iterated bubble sort (`B^k`), West's stack-sorting operator (`S`),
and pop-stack sorting (`P`) on arbitrary duplicate-free lists (`List.Nodup`):

- Operator sandwich laws:
  - `westSort_weakBruhat_bubblePass`: `S(xs) ≤_R B(xs)`
  - `westSort_weakBruhat_popSort`: `S(xs) ≤_R P(xs)`
  - `westSort_bubblePass_weakBruhat_westSort`: `S(B(xs)) ≤_R S(xs)`
  - `popSort_bubblePass_weakBruhat_popSort`: `P(B(xs)) ≤_R P(xs)`
- Non-splitting `k = 1` commutators in both `WeakBruhatLe` and `DesBotSub`:
  - `bubble_west_weakBruhat_west_bubble`: `B(S(xs)) ≤_R S(B(xs))`
  - `bubble_pop_weakBruhat_pop_bubble`: `B(P(xs)) ≤_R P(B(xs))`
  - `desBot_bubble_west_sub_west_bubble`: `DesBot(B(S(xs))) ⊆ DesBot(S(B(xs)))`
  - `desBot_bubble_pop_sub_pop_bubble`: `DesBot(B(P(xs))) ⊆ DesBot(P(B(xs)))`
- Iterated `B^k` commutator laws in `BubbleLe` (`k : Nat`):
  - `iterBubble_west_commutator`: `B^k(S(xs)) ⪯_B S(B^k(xs))`
  - `iterBubble_pop_commutator`: `B^k(P(xs)) ⪯_B P(B^k(xs))`
- Inversion-count and descent-count commutator inequalities (`invCnt`, `desCnt`) for all `k`.
- Sharp separation witnesses:
  - `exists_westSort_popSort_not_weakBruhat_mono`: neither `S` nor `P` is `≤_R`-monotone.
  - `exists_bubble_pop_incomparable`: `B` and `P` are incomparable in `≤_R`.
-/

namespace WeakBruhatCommutators

section HelperBridges

theorem weakBruhatLe_refl (xs : List Nat) : WeakBruhatLe xs xs :=
  fun _ _ h => h

theorem weakBruhatLe_trans {xs ys zs : List Nat}
    (h1 : WeakBruhatLe xs ys) (h2 : WeakBruhatLe ys zs) : WeakBruhatLe xs zs :=
  fun a b h => h2 a b (h1 a b h)

theorem desBotSub_refl (xs : List Nat) : DesBotSub xs xs :=
  fun _ h => h

theorem desBotSub_trans {xs ys zs : List Nat}
    (h1 : DesBotSub xs ys) (h2 : DesBotSub ys zs) : DesBotSub xs zs :=
  fun b h => h2 b (h1 b h)

theorem bubbleLe_refl (xs : List Nat) : BubbleLe xs xs :=
  ⟨weakBruhatLe_refl xs, desBotSub_refl xs⟩

theorem bubbleLe_trans {xs ys zs : List Nat}
    (h1 : BubbleLe xs ys) (h2 : BubbleLe ys zs) : BubbleLe xs zs :=
  ⟨weakBruhatLe_trans h1.1 h2.1, desBotSub_trans h1.2 h2.2⟩

/-- Non-inversions (`a < c` with `Before xs a c`) are preserved by `bubblePass`. -/
theorem bubblePass_before_of_lt {xs : List Nat} (hnd : xs.Nodup) {a c : Nat}
    (hlt : a < c) (hbef : Before xs a c) : Before (bubblePass xs) a c := by
  have ha : a ∈ bubblePass xs := (bubblePass_perm xs).mem_iff.mpr (mem_of_before_left hbef)
  have hc : c ∈ bubblePass xs := (bubblePass_perm xs).mem_iff.mpr (mem_of_before_right hbef)
  rcases before_or_before ha hc (by omega) with h | h
  · exact h
  · exfalso
    have hinv : IsInv xs c a := bubblePass_weakBruhat_self hnd c a ⟨hlt, h⟩
    exact before_asymm hnd hbef hinv.2

/-- If `c` precedes `b` and some `d > c` also precedes `b` in `xs`, then `c` still precedes `b`
in `bubblePass xs`. -/
theorem bubblePass_before_of_gt_before {xs : List Nat} (hnd : xs.Nodup) {c b d : Nat}
    (hcb : Before xs c b) (hcd : c < d) (hdb : Before xs d b) :
    Before (bubblePass xs) c b := by
  have hne : c ≠ b := fun h => before_irrefl hnd (h ▸ hcb)
  by_cases hlt : c < b
  · exact bubblePass_before_of_lt hnd hlt hcb
  · have hbc : b < c := by omega
    have hinv : IsInv (bubblePass xs) c b :=
      (invSet_bubblePass_iff hnd c b).mpr ⟨⟨hbc, hcb⟩, d, hcd, ⟨by omega, hdb⟩⟩
    exact hinv.2

/-- If a `Nodup` list `l` is nonempty, it has a maximum element `m ∈ l` with `∀ x ∈ l, x ≤ m`. -/
theorem exists_max_of_ne_nil : ∀ {l : List Nat}, l ≠ [] → ∃ m, m ∈ l ∧ ∀ x ∈ l, x ≤ m
  | [], h => absurd rfl h
  | [x], _ => ⟨x, by simp, fun y hy => by simp only [List.mem_singleton] at hy; omega⟩
  | x :: y :: rest, _ => by
      obtain ⟨m, hm, hle⟩ := exists_max_of_ne_nil (by simp : y :: rest ≠ [])
      by_cases hxm : m < x
      · refine ⟨x, by simp, fun z hz => ?_⟩
        simp only [List.mem_cons] at hz
        rcases hz with hzx | hz'
        · rw [hzx]; exact Nat.le_refl x
        · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hle z (by simp [hz'])) hxm)
      · refine ⟨m, by simp [hm], fun z hz => ?_⟩
        simp only [List.mem_cons] at hz
        rcases hz with hzx | hz'
        · rw [hzx]; omega
        · exact hle z (by simp [hz'])

theorem getLast?_append_of_ne_nil : ∀ (l₁ : List Nat) {l₂ : List Nat}, l₂ ≠ [] →
    (l₁ ++ l₂).getLast? = l₂.getLast?
  | [], _, _ => rfl
  | [x], l₂, h2 => by cases l₂ with | nil => exact absurd rfl h2 | cons y ys => rfl
  | x :: y :: rest, l₂, h2 => getLast?_append_of_ne_nil (y :: rest) h2

/-- Extract `l₃.getLast = x` from `l₁ ++ [x] = l₂ ++ l₃` without dependent `rw`. -/
theorem getLast_eq_of_eq_append {l₁ l₂ l₃ : List Nat} {x : Nat}
    (h : l₁ ++ [x] = l₂ ++ l₃) (h3 : l₃ ≠ []) : l₃.getLast h3 = x := by
  have hq := congrArg List.getLast? h
  rw [getLast?_append_of_ne_nil l₁ (by simp : [x] ≠ []),
      getLast?_append_of_ne_nil l₂ h3,
      List.getLast?_eq_some_getLast h3] at hq
  simp only [List.getLast?_singleton] at hq
  exact Option.some.inj hq.symm

/-- Every element strictly preceding `b` in `xs = pref ++ b :: suff` lies in `pref`. -/
theorem mem_pref_of_before {pref suff : List Nat} {b x : Nat}
    (hnd : (pref ++ b :: suff).Nodup) (h : Before (pref ++ b :: suff) x b) : x ∈ pref := by
  rcases before_append_cases hnd h with h1 | h2 | ⟨hx, _⟩
  · exact mem_of_before_left h1
  · exfalso
    have hnd2 : (b :: suff).Nodup := (List.nodup_append.mp hnd).2.1
    rcases h2 with ⟨p₁, p₂, p₃, heq⟩
    cases p₁ with
    | nil =>
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, htail⟩
        have : b ∉ suff := (List.nodup_cons.mp hnd2).1
        rw [htail] at this; exact this (by simp)
    | cons z p₁' =>
        simp only [List.cons_append, List.cons.injEq] at heq
        have : b ∉ suff := (List.nodup_cons.mp hnd2).1
        rw [heq.2] at this; exact this (by simp)
  · exact hx

/-- When the carry `m` strictly exceeds `a` and `a :: seg ++ [b]` is strictly decreasing,
`bubbleCarry m` emits `a :: seg ++ [b]` verbatim while carrying `m` past `b`. -/
theorem bubbleCarry_strictlyDec (m : Nat) : ∀ (a : Nat) (seg suff : List Nat) (b : Nat),
    a < m → StrictlyDec (a :: seg ++ [b]) →
    bubbleCarry m (a :: seg ++ b :: suff) = a :: seg ++ b :: bubbleCarry m suff
  | a, [], suff, b, ham, ⟨hba, _⟩ => by
      have hma : m > a := ham
      have hmb : m > b := Nat.lt_trans hba ham
      simp only [List.nil_append, List.cons_append, bubbleCarry, hma, hmb, ↓reduceIte]
  | a, y :: seg', suff, b, ham, ⟨hya, hsd⟩ => by
      have hma : m > a := ham
      have hmy : y < m := Nat.lt_trans hya ham
      simp only [List.cons_append, bubbleCarry, hma, ↓reduceIte]
      have ih := bubbleCarry_strictlyDec m y seg' suff b hmy hsd
      exact congrArg (a :: ·) ih

/-- Split a nonempty list `l` at its maximal strictly decreasing suffix: either `StrictlyDec l`,
or `l = headPart ++ dec` with `headPart ≠ []`, `dec ≠ []`, `StrictlyDec dec`, and
`headPart.getLast < dec.head`. -/
theorem split_max_dec_suffix : ∀ (l : List Nat), l ≠ [] → l.Nodup →
    StrictlyDec l ∨
    ∃ (hp dec : List Nat) (u v : Nat) (hhp : hp ≠ []) (hdec_ne : dec ≠ []),
      l = hp ++ dec ∧ StrictlyDec dec ∧ hp.getLast hhp = u ∧ dec.head hdec_ne = v ∧ u < v
  | [], hne, _ => absurd rfl hne
  | [_], _, _ => Or.inl trivial
  | x :: y :: rest, _, hnd => by
      have hnd' : (y :: rest).Nodup := (List.nodup_cons.mp hnd).2
      have hxy_ne : x ≠ y := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
      rcases split_max_dec_suffix (y :: rest) (by simp) hnd' with hsd | ⟨hp, dec, u, v, hhp, hdn, heq, hsd, hu, hv, huv⟩
      · by_cases hxy : x < y
        · right
          exact ⟨[x], y :: rest, x, y, by simp, by simp, rfl, hsd, rfl, rfl, hxy⟩
        · left
          exact ⟨by omega, hsd⟩
      · right
        refine ⟨x :: hp, dec, u, v, by simp, hdn, by simp [heq], hsd, ?_, hv, huv⟩
        simp [List.getLast_cons hhp, hu]

/-- Extract the adjacent predecessors `a₁` (in `y`) and `a₂` (in `bubblePass y`) of any descent
bottom `b` of `bubblePass y`, with either `a₂ = a₁` or `a₂ < a₁` and `a₂` maximizing all elements
strictly before `a₁` in `y`. -/
theorem desBot_bubblePass_witnesses {y : List Nat} (hnd : y.Nodup) {b : Nat}
    (hdesB : IsDesBot (bubblePass y) b) :
    ∃ a₁ a₂,
      b < a₁ ∧ Adj y a₁ b ∧
      b < a₂ ∧ Adj (bubblePass y) a₂ b ∧
      (a₂ = a₁ ∨ (a₂ < a₁ ∧ ∀ x, Before y x a₁ → x ≤ a₂)) := by
  have hnd_B : (bubblePass y).Nodup := ((bubblePass_perm y).nodup_iff).mpr hnd
  have hb_in : b ∈ y := by
    rcases hdesB with ⟨a, _, hadj⟩
    exact (bubblePass_perm y).mem_iff.mp (mem_of_before_right (before_of_adj hadj))
  obtain ⟨hdes_y, hli2⟩ := (desBot_bubblePass_iff hnd b).mp hdesB
  obtain ⟨pref, suff, rfl⟩ := List.append_of_mem hb_in
  have hb_notin : b ∉ pref := by
    have hdisj := (List.nodup_append.mp hnd).2.2
    intro h; exact hdisj b h b List.mem_cons_self rfl
  cases pref with
  | nil =>
      simp [leftInv] at hli2
  | cons h pref' =>
      cases pref' with
      | nil =>
          rw [leftInv_append_eq hb_notin] at hli2
          simp only [countGt] at hli2
          split at hli2 <;> omega
      | cons z pref'' =>
          have hne : z :: pref'' ≠ [] := by simp
          let a₁ := (z :: pref'').getLast hne
          let mid := (z :: pref'').dropLast
          have hsplit : z :: pref'' = mid ++ [a₁] := list_eq_dropLast_append_getLast (z :: pref'') hne
          have hy_eq : (h :: z :: pref'') ++ b :: suff = h :: mid ++ a₁ :: b :: suff := by
            rw [hsplit]; simp [List.append_assoc]
          rw [hy_eq] at hnd hnd_B hdesB hdes_y hli2 ⊢
          let m := listMax h mid
          have hadj_a1 : Adj (h :: mid ++ a₁ :: b :: suff) a₁ b := ⟨h :: mid, suff, by simp⟩
          have hba1 : b < a₁ := by
            rcases hdes_y with ⟨a, hba, hadj⟩
            rw [← adj_left_unique hnd hadj hadj_a1]; exact hba
          have hpred := bubblePass_adj_pred h a₁ b mid suff
          by_cases hma1 : m > a₁
          · have hmb : m > b := Nat.lt_trans hba1 hma1
            have hadjB : Adj (bubblePass (h :: mid ++ a₁ :: b :: suff)) a₁ b :=
              hpred.1 ⟨hma1, hmb⟩
            exact ⟨a₁, a₁, hba1, hadj_a1, hba1, hadjB, Or.inl rfl⟩
          · have hadjB : Adj (bubblePass (h :: mid ++ a₁ :: b :: suff)) m b :=
              hpred.2 ⟨by omega, hba1⟩
            have hbm : b < m := by
              rcases hdesB with ⟨a, hba, hadj⟩
              rw [← adj_left_unique hnd_B hadj hadjB]; exact hba
            have hne_ma1 : m ≠ a₁ := by
              have hm_mem : m ∈ h :: mid := listMax_mem h mid
              have hnd' : ((h :: mid) ++ a₁ :: (b :: suff)).Nodup := by
                simpa [List.append_assoc] using hnd
              exact (List.nodup_append.mp hnd').2.2 m hm_mem a₁ List.mem_cons_self
            refine ⟨a₁, m, hba1, hadj_a1, hbm, hadjB, Or.inr ⟨by omega, ?_⟩⟩
            intro x hxa1
            have hnd' : ((h :: mid) ++ a₁ :: (b :: suff)).Nodup := by
              simpa [List.append_assoc] using hnd
            have hx_in : x ∈ h :: mid :=
              mem_pref_of_before hnd' (by simpa [List.append_assoc] using hxa1)
            simp only [List.mem_cons] at hx_in
            rcases hx_in with rfl | hx_mid
            · exact le_listMax x mid
            · exact mem_le_listMax h hx_mid

end HelperBridges

section SandwichLaws

/-- **Sandwich Theorem 1 (`westSort_weakBruhat_bubblePass`):** `S(xs) ≤_R B(xs)` for every `Nodup`
list `xs`. -/
theorem westSort_weakBruhat_bubblePass {xs : List Nat} (hnd : xs.Nodup) :
    WeakBruhatLe (westSort xs) (bubblePass xs) := by
  intro a b h
  obtain ⟨hab, c, hac, _, hcb⟩ := (invSet_westSort_iff hnd a b).mp h
  exact (invSet_bubblePass_iff hnd a b).mpr ⟨hab, c, hac, ⟨Nat.lt_trans hab.1 hac, hcb⟩⟩

/-- **Sandwich Theorem 2 (`westSort_weakBruhat_popSort`):** `S(xs) ≤_R P(xs)` for every `Nodup`
list `xs`. -/
theorem westSort_weakBruhat_popSort {xs : List Nat} (hnd : xs.Nodup) :
    WeakBruhatLe (westSort xs) (popSort xs) := by
  intro a b h
  obtain ⟨hab, c, hac, hac_b, hcb_b⟩ := (invSet_westSort_iff hnd a b).mp h
  rw [invSet_popSort_iff hnd a b]
  refine ⟨hab, hasAscentBetween_extend_right hnd (hasAscentBetween_of_lt hnd hac hac_b) hcb_b⟩

/-- **Monotone Dominance 1 (`westSort_bubblePass_weakBruhat_westSort`):**
`S(B(xs)) ≤_R S(xs)` for every `Nodup` list `xs`. -/
theorem westSort_bubblePass_weakBruhat_westSort {xs : List Nat} (hnd : xs.Nodup) :
    WeakBruhatLe (westSort (bubblePass xs)) (westSort xs) := by
  have hnd_B : (bubblePass xs).Nodup := ((bubblePass_perm xs).nodup_iff).mpr hnd
  intro a b h
  obtain ⟨hab_B, c, hac, hac_B, hcb_B⟩ := (invSet_westSort_iff hnd_B a b).mp h
  have hab : IsInv xs a b := bubblePass_weakBruhat_self hnd a b hab_B
  have hcb_inv_B : IsInv (bubblePass xs) c b := ⟨Nat.lt_trans hab.1 hac, hcb_B⟩
  obtain ⟨hcb, d, hcd, hdb⟩ := (invSet_bubblePass_iff hnd c b).mp hcb_inv_B
  rw [invSet_westSort_iff hnd a b]
  refine ⟨hab, ?_⟩
  have ha_mem : a ∈ xs := mem_of_before_left hab.2
  have hc_mem : c ∈ xs := mem_of_before_left hcb.2
  rcases before_or_before ha_mem hc_mem (by omega) with hac_xs | hca_xs
  · exact ⟨c, hac, hac_xs, hcb.2⟩
  · -- `c` preceded `a` in `xs`, yet `a` precedes `c` in `B(xs)`, so `¬ IsInv (B xs) c a`.
    -- Thus no `z > c` precedes `a` in `xs`; in particular `d > c` must appear AFTER `a` in `xs`!
    have hnot_ca_B : ¬ IsInv (bubblePass xs) c a := fun hinv => before_asymm hnd_B hac_B hinv.2
    have hd_mem : d ∈ xs := mem_of_before_left hdb.2
    have had_xs : Before xs a d := by
      rcases before_or_before ha_mem hd_mem (by omega) with h1 | h2
      · exact h1
      · exfalso
        exact hnot_ca_B ((invSet_bubblePass_iff hnd c a).mpr ⟨⟨hac, hca_xs⟩, d, hcd, ⟨by omega, h2⟩⟩)
    exact ⟨d, Nat.lt_trans hac hcd, had_xs, hdb.2⟩

/-- **Monotone Dominance 2 (`popSort_bubblePass_weakBruhat_popSort`):**
`P(B(xs)) ≤_R P(xs)` for every `Nodup` list `xs`. -/
theorem popSort_bubblePass_weakBruhat_popSort {xs : List Nat} (hnd : xs.Nodup) :
    WeakBruhatLe (popSort (bubblePass xs)) (popSort xs) := by
  have hnd_B : (bubblePass xs).Nodup := ((bubblePass_perm xs).nodup_iff).mpr hnd
  intro a b h
  obtain ⟨hab_B, hasc_B⟩ := (invSet_popSort_iff hnd_B a b).mp h
  obtain ⟨hab, c, hac, hcb⟩ := (invSet_bubblePass_iff hnd a b).mp hab_B
  rw [invSet_popSort_iff hnd a b]
  refine ⟨hab, ?_⟩
  rcases hab with ⟨hba, l₁, l₂, l₃, rfl⟩
  rw [hasAscentBetween_iff_not_strictlyDec hnd]
  intro hdec
  -- Since `c > a` precedes `b` and `a :: l₂ ++ [b]` is strictly decreasing, `c` must lie in `l₁`!
  have hc_in_l1 : c ∈ l₁ := by
    have hnd' : ((l₁ ++ a :: l₂) ++ b :: l₃).Nodup := by simpa [List.append_assoc] using hnd
    have hc_pref : c ∈ l₁ ++ a :: l₂ := mem_pref_of_before hnd' (by simpa [List.append_assoc] using hcb.2)
    simp only [List.mem_append, List.mem_cons] at hc_pref
    rcases hc_pref with hc1 | rfl | hc2
    · exact hc1
    · omega
    · exfalso
      obtain ⟨p₁, p₂, rfl⟩ := List.append_of_mem hc2
      have hac_gt : c < a := strictlyDec_before_gt hdec ⟨[], p₁, p₂ ++ [b], by simp [List.append_assoc]⟩
      omega
  cases l₁ with
  | nil => simp at hc_in_l1
  | cons x l₁' =>
      obtain ⟨out, heq, _⟩ := bubbleCarry_append x l₁' (a :: l₂ ++ b :: l₃)
      have hbp : bubblePass ((x :: l₁') ++ a :: l₂ ++ b :: l₃) =
          out ++ bubbleCarry (listMax x l₁') (a :: l₂ ++ b :: l₃) := by
        simpa [bubblePass, List.append_assoc] using heq
      have ham : a < listMax x l₁' := by
        simp only [List.mem_cons] at hc_in_l1
        rcases hc_in_l1 with rfl | hc1'
        · exact Nat.lt_of_lt_of_le hac (le_listMax c l₁')
        · exact Nat.lt_of_lt_of_le hac (mem_le_listMax x hc1')
      have hcarry := bubbleCarry_strictlyDec (listMax x l₁') a l₂ l₃ b ham hdec
      have hbp_final : bubblePass ((x :: l₁') ++ a :: l₂ ++ b :: l₃) =
          out ++ a :: l₂ ++ b :: bubbleCarry (listMax x l₁') l₃ := by
        rw [hbp, hcarry]; simp [List.append_assoc]
      rw [hbp_final] at hnd_B hasc_B
      have hnotdec := (hasAscentBetween_iff_not_strictlyDec hnd_B).mp hasc_B
      exact hnotdec hdec

end SandwichLaws

section OneStepCommutators

/-- Helper: if `IsInv (westSort xs) a b` and some `d > a` precedes `a` in `xs`, then
`IsInv (westSort (bubblePass xs)) a b`. -/
theorem inv_west_bubble_of_gt_before_left {xs : List Nat} (hnd : xs.Nodup) {a b d : Nat}
    (hab_S : IsInv (westSort xs) a b) (had : a < d) (hda : Before xs d a) :
    IsInv (westSort (bubblePass xs)) a b := by
  have hnd_B : (bubblePass xs).Nodup := ((bubblePass_perm xs).nodup_iff).mpr hnd
  obtain ⟨hab, e, hae, hae_b, heb_b⟩ := (invSet_westSort_iff hnd a b).mp hab_S
  rw [invSet_westSort_iff hnd_B a b]
  refine ⟨(invSet_bubblePass_iff hnd a b).mpr ⟨hab, e, hae, ⟨Nat.lt_trans hab.1 hae, heb_b⟩⟩, ?_⟩
  -- Let `M` be the maximum element strictly before `b` in `xs`:
  obtain ⟨pref, suff, rfl⟩ := List.append_of_mem (mem_of_before_right hab.2)
  have ha_pref : a ∈ pref := mem_pref_of_before hnd hab.2
  have he_pref : e ∈ pref := mem_pref_of_before hnd heb_b
  have hd_pref : d ∈ pref := mem_pref_of_before hnd (before_trans hnd hda hab.2)
  have hpref_ne : pref ≠ [] := fun h => by subst h; simp at ha_pref
  obtain ⟨M, hM_pref, hM_max⟩ := exists_max_of_ne_nil hpref_ne
  have hMb : Before (pref ++ b :: suff) M b := before_append_of_mem hM_pref List.mem_cons_self
  have he_le_M : e ≤ M := hM_max e he_pref
  have hd_le_M : d ≤ M := hM_max d hd_pref
  by_cases heM : e < M
  · exact ⟨e, hae, bubblePass_before_of_lt hnd hae hae_b,
      bubblePass_before_of_gt_before hnd heb_b heM hMb⟩
  · -- `e = M`: let `y` be the maximum element strictly before `a` in `xs` (`a < d ≤ y < M = e`)!
    have hEq : e = M := by omega
    obtain ⟨prefa, suffa, hpa⟩ := List.append_of_mem (mem_of_before_left hab.2)
    have hnd_a : (prefa ++ a :: suffa).Nodup := hpa ▸ hnd
    have hd_pa : d ∈ prefa := mem_pref_of_before hnd_a (hpa ▸ hda)
    have hpa_ne : prefa ≠ [] := fun h => by subst h; simp at hd_pa
    obtain ⟨y, hy_pa, hy_max⟩ := exists_max_of_ne_nil hpa_ne
    have hya_bef : Before (pref ++ b :: suff) y a := by
      rw [hpa]; exact before_append_of_mem hy_pa List.mem_cons_self
    have hdy : d ≤ y := hy_max d hd_pa
    have hay : a < y := Nat.lt_of_lt_of_le had hdy
    have hyb_bef : Before (pref ++ b :: suff) y b := before_trans hnd hya_bef hab.2
    have hy_pref : y ∈ pref := mem_pref_of_before hnd hyb_bef
    have hy_le_M : y ≤ M := hM_max y hy_pref
    have hy_ne_M : y ≠ M := by
      intro heqy
      rw [← hEq] at heqy
      rw [heqy] at hya_bef
      exact before_asymm hnd hae_b hya_bef
    have hy_lt_M : y < M := by omega
    have hay_B : Before (bubblePass (pref ++ b :: suff)) a y := by
      have ha_B : a ∈ bubblePass (pref ++ b :: suff) :=
        (bubblePass_perm _).mem_iff.mpr (mem_of_before_left hab.2)
      have hy_B : y ∈ bubblePass (pref ++ b :: suff) :=
        (bubblePass_perm _).mem_iff.mpr (mem_of_before_left hyb_bef)
      rcases before_or_before ha_B hy_B (by omega) with h1 | h2
      · exact h1
      · exfalso
        obtain ⟨_, z, hyz, hza⟩ := (invSet_bubblePass_iff hnd y a).mp ⟨hay, h2⟩
        have hz_pa : z ∈ prefa := mem_pref_of_before hnd_a (hpa ▸ hza.2)
        have := hy_max z hz_pa; omega
    exact ⟨y, hay, hay_B, bubblePass_before_of_gt_before hnd hyb_bef hy_lt_M hMb⟩

/-- **Main Commutator Theorem 1 (`bubble_west_weakBruhat_west_bubble`):**
`B(S(xs)) ≤_R S(B(xs))` for every duplicate-free list `xs`. -/
theorem bubble_west_weakBruhat_west_bubble {xs : List Nat} (hnd : xs.Nodup) :
    WeakBruhatLe (bubblePass (westSort xs)) (westSort (bubblePass xs)) := by
  have hnd_S : (westSort xs).Nodup := ((westSort_perm xs).nodup_iff).mpr hnd
  have hnd_B : (bubblePass xs).Nodup := ((bubblePass_perm xs).nodup_iff).mpr hnd
  intro a b h
  obtain ⟨hab_S, c₂, hac₂, hc₂b_S⟩ := (invSet_bubblePass_iff hnd_S a b).mp h
  obtain ⟨hab, c₁, hac₁, hac₁_b, hc₁b_b⟩ := (invSet_westSort_iff hnd a b).mp hab_S
  obtain ⟨hc₂b, d, hc₂d, _, hdb_b⟩ := (invSet_westSort_iff hnd c₂ b).mp hc₂b_S
  -- Check whether `c₂` lies before `a` or after `a` in `xs`:
  have ha_mem : a ∈ xs := mem_of_before_left hab.2
  have hc₂_mem : c₂ ∈ xs := mem_of_before_left hc₂b.2
  rcases before_or_before ha_mem hc₂_mem (by omega) with hac₂_b | hc₂a_b
  · -- `c₂` lies between `a` and `b` in `xs`, AND `d > c₂` precedes `b` in `xs`!
    rw [invSet_westSort_iff hnd_B a b]
    refine ⟨(invSet_bubblePass_iff hnd a b).mpr ⟨hab, c₁, hac₁, ⟨Nat.lt_trans hab.1 hac₁, hc₁b_b⟩⟩,
      c₂, hac₂,
      bubblePass_before_of_lt hnd hac₂ hac₂_b,
      bubblePass_before_of_gt_before hnd hc₂b.2 hc₂d hdb_b⟩
  · -- `c₂ > a` precedes `a` in `xs`: apply `inv_west_bubble_of_gt_before_left`!
    exact inv_west_bubble_of_gt_before_left hnd hab_S hac₂ hc₂a_b

/-- **Main Commutator Theorem 2 (`bubble_pop_weakBruhat_pop_bubble`):**
`B(P(xs)) ≤_R P(B(xs))` for every duplicate-free list `xs`. -/
theorem bubble_pop_weakBruhat_pop_bubble {xs : List Nat} (hnd : xs.Nodup) :
    WeakBruhatLe (bubblePass (popSort xs)) (popSort (bubblePass xs)) := by
  have hnd_P : (popSort xs).Nodup := ((popSort_perm xs).nodup_iff).mpr hnd
  have hnd_B : (bubblePass xs).Nodup := ((bubblePass_perm xs).nodup_iff).mpr hnd
  intro a b h
  obtain ⟨hab_P, c, hac, hcb_P⟩ := (invSet_bubblePass_iff hnd_P a b).mp h
  obtain ⟨hab, hasc_ab⟩ := (invSet_popSort_iff hnd a b).mp hab_P
  obtain ⟨hcb, hasc_cb⟩ := (invSet_popSort_iff hnd c b).mp hcb_P
  rw [invSet_popSort_iff hnd_B a b]
  refine ⟨(invSet_bubblePass_iff hnd a b).mpr ⟨hab, c, hac, hcb⟩, ?_⟩
  -- Split `xs = pre ++ b :: suff`, and split `pre ++ [b]` at its maximal strictly decreasing suffix `dec`:
  obtain ⟨pre, suff, rfl⟩ := List.append_of_mem (mem_of_before_right hab.2)
  have hnd_pb : (pre ++ [b]).Nodup := by
    have h1 : ((pre ++ [b]) ++ suff).Nodup := by simpa [List.append_assoc] using hnd
    exact (List.nodup_append.mp h1).1
  rcases split_max_dec_suffix (pre ++ [b]) (by simp) hnd_pb with hdec | ⟨hp, dec, u, v, hhp, hdn, hsplit, hdec_sd, hu, hv, huv⟩
  · -- Impossible: `pre ++ [b]` is strictly decreasing, contradicting `HasAscentBetween xs a b`!
    exfalso
    rcases hab.2 with ⟨l₁, l₂, l₃, heq⟩
    have hnd1 : (pre ++ b :: suff).Nodup := hnd
    have h1 : pre ++ b :: suff = (l₁ ++ a :: l₂) ++ b :: l₃ := by simpa [List.append_assoc] using heq
    obtain ⟨hl, _⟩ := append_cons_eq_unique hnd1 h1
    have hdec_sub : StrictlyDec (a :: l₂ ++ [b]) := by
      have : pre ++ [b] = l₁ ++ (a :: l₂ ++ [b]) := by rw [hl]; simp [List.append_assoc]
      rw [this] at hdec
      exact strictlyDec_append_right hdec
    have hnotdec := (hasAscentBetween_iff_not_strictlyDec (by rw [← heq]; exact hnd)).mp
      (by rw [← heq]; exact hasc_ab)
    exact hnotdec hdec_sub
  · -- `pre ++ [b] = hp ++ dec`, `hp ≠ []`, `dec ≠ []`, `StrictlyDec dec`, `u = hp.getLast < dec.head = v`!
    have hxs_eq : pre ++ b :: suff = hp ++ dec ++ suff := by
      have : pre ++ b :: suff = (pre ++ [b]) ++ suff := by simp [List.append_assoc]
      rw [this, hsplit]
    -- Show neither `a` nor `c` lies in `dec`:
    have hdec_last : dec.getLast hdn = b := getLast_eq_of_eq_append hsplit hdn
    have hnot_in_dec : ∀ x, HasAscentBetween (pre ++ b :: suff) x b → x ∈ pre → x ∉ dec := by
      intro x hasc_xb _ hx_dec
      obtain ⟨q₁, q₂, hq⟩ := List.append_of_mem hx_dec
      have hxb_ne : x ≠ b := by
        rcases hasc_xb with ⟨p₁, p₂, p₃, _, _, heq, _, _⟩
        intro hxbeq; subst hxbeq
        exact before_irrefl hnd ⟨p₁, p₂, p₃, heq⟩
      have hq2_ne : q₂ ≠ [] := by
        intro hnil; subst hnil
        have h1 : dec.getLast hdn = x := by
          have hq' : dec = q₁ ++ [x] := hq
          have hlast := congrArg List.getLast? hq'
          rw [getLast?_append_of_ne_nil q₁ (by simp : [x] ≠ []),
              List.getLast?_eq_some_getLast hdn] at hlast
          simp only [List.getLast?_singleton] at hlast
          exact Option.some.inj hlast
        exact hxb_ne (h1.symm.trans hdec_last)
      have hq2_split : q₂ = q₂.dropLast ++ [b] := by
        have hq2_last : q₂.getLast hq2_ne = b := by
          have hdec_eq : dec = dec.dropLast ++ [b] := by
            rw [← hdec_last]; exact list_eq_dropLast_append_getLast dec hdn
          have h1 : dec.dropLast ++ [b] = (q₁ ++ [x]) ++ q₂ := by
            rw [← hdec_eq, hq]; simp [List.append_assoc]
          exact getLast_eq_of_eq_append h1 hq2_ne
        rw [← hq2_last]; exact list_eq_dropLast_append_getLast q₂ hq2_ne
      have heq_full : pre ++ b :: suff = (hp ++ q₁) ++ x :: q₂.dropLast ++ b :: suff := by
        rw [hxs_eq, hq, hq2_split]; simp [List.append_assoc]
      have hnd_full : ((hp ++ q₁) ++ x :: q₂.dropLast ++ b :: suff).Nodup := heq_full ▸ hnd
      have hnotdec := (hasAscentBetween_iff_not_strictlyDec hnd_full).mp (heq_full ▸ hasc_xb)
      have hsd_sub : StrictlyDec (x :: q₂.dropLast ++ [b]) := by
        have : dec = q₁ ++ (x :: q₂.dropLast ++ [b]) := by
          rw [hq, hq2_split]; simp
        rw [this] at hdec_sd
        exact strictlyDec_append_right hdec_sd
      exact hnotdec hsd_sub
    have ha_pref : a ∈ pre := mem_pref_of_before hnd hab.2
    have hc_pref : c ∈ pre := mem_pref_of_before hnd hcb.2
    have ha_hp : a ∈ hp := by
      have ha_pb : a ∈ pre ++ [b] := by simp [ha_pref]
      rw [hsplit, List.mem_append] at ha_pb
      exact ha_pb.resolve_right (hnot_in_dec a hasc_ab ha_pref)
    have hc_hp : c ∈ hp := by
      have hc_pb : c ∈ pre ++ [b] := by simp [hc_pref]
      rw [hsplit, List.mem_append] at hc_pb
      exact hc_pb.resolve_right (hnot_in_dec c hasc_cb hc_pref)
    -- `hp` contains two distinct elements `a < c`, so `hp = h :: hp_mid ++ [u]`!
    have hhp_split : hp = hp.dropLast ++ [u] := by
      rw [← hu]; exact list_eq_dropLast_append_getLast hp hhp
    have hhp_dl_ne : hp.dropLast ≠ [] := by
      intro hnil
      rw [hnil, List.nil_append] at hhp_split
      rw [hhp_split, List.mem_singleton] at ha_hp hc_hp
      omega
    obtain ⟨h0, mid, hdl_eq⟩ : ∃ h0 mid, hp.dropLast = h0 :: mid := by
      cases hdl : hp.dropLast with
      | nil => exact absurd hdl hhp_dl_ne
      | cons h0 mid => exact ⟨h0, mid, rfl⟩
    have hhp_eq : hp = (h0 :: mid) ++ [u] := by rw [← hdl_eq]; exact hhp_split
    obtain ⟨v', dtail, hdec_cons⟩ : ∃ v' dtail, dec = v' :: dtail := by
      cases dec with
      | nil => exact absurd rfl hdn
      | cons v' dtail => exact ⟨v', dtail, rfl⟩
    have hv' : v' = v := by simp [hdec_cons] at hv; exact hv
    rw [hv'] at hdec_cons
    have hb_in_dec : b ∈ v :: dtail := by
      have hb_mem_dec : b ∈ dec := by
        rw [← hdec_last]; exact List.getLast_mem hdn
      rw [← hdec_cons]; exact hb_mem_dec
    -- Now trace `bubblePass` across `(h0 :: mid) ++ u :: v :: dtail ++ suff`!
    have hxs_full : pre ++ b :: suff = h0 :: mid ++ u :: v :: (dtail ++ suff) := by
      rw [hxs_eq, hhp_eq, hdec_cons]; simp [List.append_assoc]
    obtain ⟨out, heq_bc, hperm_bc⟩ := bubbleCarry_append h0 mid (u :: v :: (dtail ++ suff))
    let m := listMax h0 mid
    have hbp_eq : bubblePass (pre ++ b :: suff) =
        out ++ bubbleCarry m (u :: v :: (dtail ++ suff)) := by
      rw [hxs_full]; simpa [bubblePass, m] using heq_bc
    have hm_ge_ac : a < m ∨ a < u := by
      rw [hhp_eq, List.mem_append, List.mem_singleton] at hc_hp
      rcases hc_hp with hc_hm | rfl
      · left
        simp only [List.mem_cons] at hc_hm
        rcases hc_hm with rfl | hc_mid
        · exact Nat.lt_of_lt_of_le hac (le_listMax c mid)
        · exact Nat.lt_of_lt_of_le hac (mem_le_listMax h0 hc_mid)
      · right; exact hac
    by_cases hmu : m > u
    · -- `m > u`: `bubbleCarry m` emits `u`, then emits `min(m, v) > u`!
      have ha_lt_m : a < m := by rcases hm_ge_ac with h1 | h2 <;> omega
      have ha_in_out_u : a ∈ out ++ [u] := by
        rw [hhp_eq, List.mem_append, List.mem_singleton] at ha_hp
        rcases ha_hp with ha_hm | rfl
        · have ha_outm : a ∈ out ++ [m] := hperm_bc.mem_iff.mpr ha_hm
          simp only [List.mem_append, List.mem_singleton] at ha_outm
          rcases ha_outm with h1 | h2
          · exact List.mem_append_left [u] h1
          · omega
        · simp
      have hbp1 : bubblePass (pre ++ b :: suff) =
          (out ++ [u]) ++ bubbleCarry m (v :: (dtail ++ suff)) := by
        have hstep : bubbleCarry m (u :: v :: (dtail ++ suff)) =
            u :: bubbleCarry m (v :: (dtail ++ suff)) := by
          rw [bubbleCarry]; simp only [hmu, ↓reduceIte]
        rw [hbp_eq, hstep]; simp [List.append_assoc]
      by_cases hmv : m > v
      · -- Emits `v` next: `u < v` is adjacent between `a` and `b`!
        have hbp2 : bubblePass (pre ++ b :: suff) =
            out ++ u :: v :: bubbleCarry m (dtail ++ suff) := by
          have hstep : bubbleCarry m (v :: (dtail ++ suff)) =
              v :: bubbleCarry m (dtail ++ suff) := by
            rw [bubbleCarry]; simp only [hmv, ↓reduceIte]
          rw [hbp1, hstep]; simp [List.append_assoc]
        have hb_in_rest : b ∈ v :: bubbleCarry m (dtail ++ suff) := by
          simp only [List.mem_cons] at hb_in_dec ⊢
          rcases hb_in_dec with rfl | hb_dt
          · exact Or.inl rfl
          · right; exact (bubbleCarry_perm m (dtail ++ suff)).mem_iff.mpr (by simp [hb_dt])
        -- Split `out ++ [u]` at `a` and `v :: bubbleCarry m (dtail ++ suff)` at `b`:
        obtain ⟨p₁, p₂, hp_a⟩ := List.append_of_mem ha_in_out_u
        obtain ⟨q₁, q₂, hq_b⟩ := List.append_of_mem hb_in_rest
        have hbp3 : bubblePass (pre ++ b :: suff) = p₁ ++ a :: (p₂ ++ q₁) ++ b :: q₂ := by
          rw [hbp2]
          have : out ++ u :: v :: bubbleCarry m (dtail ++ suff) =
              (out ++ [u]) ++ (v :: bubbleCarry m (dtail ++ suff)) := by simp [List.append_assoc]
          rw [this, hp_a, hq_b]; simp [List.append_assoc]
        have hne_ap2 : a :: p₂ ≠ [] := by simp
        have hlast_ap2 : (a :: p₂).getLast hne_ap2 = u := getLast_eq_of_eq_append hp_a hne_ap2
        have hsplit_ap2 : a :: p₂ = (a :: p₂).dropLast ++ [u] := by
          rw [← hlast_ap2]; exact list_eq_dropLast_append_getLast (a :: p₂) hne_ap2
        have hq1_head : q₁ ++ [b] = v :: (q₁ ++ [b]).tail := by
          cases q₁ with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at hq_b ⊢
              exact ⟨hq_b.1.symm, rfl⟩
          | cons w q₁' =>
              simp only [List.cons_append, List.cons.injEq] at hq_b ⊢
              exact ⟨hq_b.1.symm, rfl⟩
        refine ⟨p₁, p₂ ++ q₁, q₂, u, v, hbp3, huv, (a :: p₂).dropLast, (q₁ ++ [b]).tail, ?_⟩
        calc a :: (p₂ ++ q₁) ++ [b]
            = (a :: p₂) ++ (q₁ ++ [b]) := by simp [List.append_assoc]
          _ = ((a :: p₂).dropLast ++ [u]) ++ (v :: (q₁ ++ [b]).tail) := by rw [← hsplit_ap2, ← hq1_head]
          _ = (a :: p₂).dropLast ++ u :: v :: (q₁ ++ [b]).tail := by simp [List.append_assoc]
      · -- `m ≤ v`: emits `m` next, and `u < m`, with `b ∈ bubbleCarry v (dtail ++ suff)`!
        have hbp2 : bubblePass (pre ++ b :: suff) =
            (out ++ [u]) ++ m :: bubbleCarry v (dtail ++ suff) := by
          have hstep : bubbleCarry m (v :: (dtail ++ suff)) =
              m :: bubbleCarry v (dtail ++ suff) := by
            rw [bubbleCarry]; simp only [hmv, ↓reduceIte]
          rw [hbp1, hstep]
        have hb_in_rest : b ∈ bubbleCarry v (dtail ++ suff) := by
          exact (bubbleCarry_perm v (dtail ++ suff)).mem_iff.mpr (by
            simp only [List.mem_cons] at hb_in_dec ⊢
            rcases hb_in_dec with rfl | hb_dt
            · exact Or.inl rfl
            · exact Or.inr (List.mem_append_left suff hb_dt))
        obtain ⟨p₁, p₂, hp_a⟩ := List.append_of_mem ha_in_out_u
        obtain ⟨q₁, q₂, hq_b⟩ := List.append_of_mem hb_in_rest
        have hbp3 : bubblePass (pre ++ b :: suff) = p₁ ++ a :: (p₂ ++ m :: q₁) ++ b :: q₂ := by
          rw [hbp2, hp_a, hq_b]; simp [List.append_assoc]
        have hne_ap2 : a :: p₂ ≠ [] := by simp
        have hlast_ap2 : (a :: p₂).getLast hne_ap2 = u := getLast_eq_of_eq_append hp_a hne_ap2
        have hsplit_ap2 : a :: p₂ = (a :: p₂).dropLast ++ [u] := by
          rw [← hlast_ap2]; exact list_eq_dropLast_append_getLast (a :: p₂) hne_ap2
        refine ⟨p₁, p₂ ++ m :: q₁, q₂, u, m, hbp3, hmu, (a :: p₂).dropLast, q₁ ++ [b], ?_⟩
        calc a :: (p₂ ++ m :: q₁) ++ [b]
            = (a :: p₂) ++ m :: (q₁ ++ [b]) := by simp [List.append_assoc]
          _ = ((a :: p₂).dropLast ++ [u]) ++ m :: (q₁ ++ [b]) := by rw [← hsplit_ap2]
          _ = (a :: p₂).dropLast ++ u :: m :: (q₁ ++ [b]) := by simp [List.append_assoc]
    · -- `m ≤ u`: `bubblePass` emits `(out ++ [m]) ++ u :: bubbleCarry v (dtail ++ suff)`!
      -- Since `a < c` and `c ≤ max(m, u) = u`, we have `a < u` and `a ∈ h0 :: mid`, so `a ∈ out ++ [m]`!
      have hau : a < u := by rcases hm_ge_ac with h1 | h2 <;> omega
      have ha_in_outm : a ∈ out ++ [m] := by
        rw [hhp_eq, List.mem_append, List.mem_singleton] at ha_hp
        rcases ha_hp with ha_hm | rfl
        · exact hperm_bc.mem_iff.mpr ha_hm
        · omega
      have hnot_uv : ¬ (u > v) := by omega
      have hbp2 : bubblePass (pre ++ b :: suff) =
          (out ++ [m]) ++ u :: bubbleCarry v (dtail ++ suff) := by
        have hstep1 : bubbleCarry m (u :: v :: (dtail ++ suff)) =
            m :: bubbleCarry u (v :: (dtail ++ suff)) := by
          rw [bubbleCarry]; simp only [hmu, ↓reduceIte]
        have hstep2 : bubbleCarry u (v :: (dtail ++ suff)) =
            u :: bubbleCarry v (dtail ++ suff) := by
          rw [bubbleCarry]; simp only [hnot_uv, ↓reduceIte]
        rw [hbp_eq, hstep1, hstep2]; simp [List.append_assoc]
      have hb_in_rest : b ∈ bubbleCarry v (dtail ++ suff) := by
        exact (bubbleCarry_perm v (dtail ++ suff)).mem_iff.mpr (by
          simp only [List.mem_cons] at hb_in_dec ⊢
          rcases hb_in_dec with rfl | hb_dt
          · exact Or.inl rfl
          · exact Or.inr (List.mem_append_left suff hb_dt))
      have hau_B : Before (bubblePass (pre ++ b :: suff)) a u := by
        rw [hbp2]; exact before_append_of_mem ha_in_outm List.mem_cons_self
      have hub_B : Before (bubblePass (pre ++ b :: suff)) u b := by
        rw [hbp2]
        obtain ⟨q₁, q₂, hq⟩ := List.append_of_mem hb_in_rest
        exact ⟨out ++ [m], q₁, q₂, by rw [hq]; simp [List.append_assoc]⟩
      exact hasAscentBetween_extend_right hnd_B (hasAscentBetween_of_lt hnd_B hau hau_B) hub_B

/-- **Universal Right-Valley Transfer for `westSort`:**
If `b ∈ DesBot(westSort xs)` and `∃ a, IsInv xs a b`, then every right-inversion `(b, z)` of
`westSort xs` remains an inversion of `westSort (bubblePass xs)`. -/
theorem rightValley_transfer_west {xs : List Nat} (hnd : xs.Nodup) {b z : Nat}
    (hdes_S : IsDesBot (westSort xs) b) (hinv_xs : ∃ a, IsInv xs a b)
    (hbz_S : IsInv (westSort xs) b z) : IsInv (westSort (bubblePass xs)) b z := by
  have hnd_B : (bubblePass xs).Nodup := ((bubblePass_perm xs).nodup_iff).mpr hnd
  have hrv_xs : IsRightValley xs b := rightValley_of_isDesBot_westSort hnd hdes_S
  have hrv_B : IsRightValley (bubblePass xs) b := rightValley_bubblePass hnd hrv_xs hinv_xs
  have hbz_xs : IsInv xs b z := westSort_weakBruhat_self hnd b z hbz_S
  rcases hinv_xs with ⟨a, hba, hab⟩
  have hbz_B : IsInv (bubblePass xs) b z :=
    (invSet_bubblePass_iff hnd b z).mpr ⟨hbz_xs, a, hba, ⟨Nat.lt_trans hbz_xs.1 hba, before_trans hnd hab hbz_xs.2⟩⟩
  exact inv_rightValley_westSort hnd_B hrv_B hbz_B

/-- **Universal Right-Valley Transfer for `popSort`:**
If `b ∈ DesBot(popSort xs)` and `∃ a, IsInv xs a b`, then every right-inversion `(b, z)` of
`popSort xs` remains an inversion of `popSort (bubblePass xs)`. -/
theorem rightValley_transfer_pop {xs : List Nat} (hnd : xs.Nodup) {b z : Nat}
    (hdes_P : IsDesBot (popSort xs) b) (hinv_xs : ∃ a, IsInv xs a b)
    (hbz_P : IsInv (popSort xs) b z) : IsInv (popSort (bubblePass xs)) b z := by
  have hnd_B : (bubblePass xs).Nodup := ((bubblePass_perm xs).nodup_iff).mpr hnd
  have hrv_xs : IsRightValley xs b := rightValley_of_isDesBot_popSort hnd hdes_P
  have hrv_B : IsRightValley (bubblePass xs) b := rightValley_bubblePass hnd hrv_xs hinv_xs
  have hbz_xs : IsInv xs b z := popSort_weakBruhat_self hnd b z hbz_P
  rcases hinv_xs with ⟨a, hba, hab⟩
  have hbz_B : IsInv (bubblePass xs) b z :=
    (invSet_bubblePass_iff hnd b z).mpr ⟨hbz_xs, a, hba, ⟨Nat.lt_trans hbz_xs.1 hba, before_trans hnd hab hbz_xs.2⟩⟩
  exact inv_rightValley_popSort hnd_B hrv_B hbz_B

/-- **Main Descent-Bottom Commutator 1 (`desBot_bubble_west_sub_west_bubble`):**
`DesBot(B(S(xs))) ⊆ DesBot(S(B(xs)))` for every duplicate-free list `xs`. -/
theorem desBot_bubble_west_sub_west_bubble {xs : List Nat} (hnd : xs.Nodup) :
    DesBotSub (bubblePass (westSort xs)) (westSort (bubblePass xs)) := by
  have hnd_S : (westSort xs).Nodup := ((westSort_perm xs).nodup_iff).mpr hnd
  have hnd_B : (bubblePass xs).Nodup := ((bubblePass_perm xs).nodup_iff).mpr hnd
  have hnd_SB : (westSort (bubblePass xs)).Nodup := ((westSort_perm _).nodup_iff).mpr hnd_B
  intro b hdes_BS
  obtain ⟨a₁, a₂, hba₁, hadj₁, hba₂, hadj₂, hcase⟩ := desBot_bubblePass_witnesses hnd_S hdes_BS
  have hdes_S : IsDesBot (westSort xs) b := ⟨a₁, hba₁, hadj₁⟩
  have hab₁_S : IsInv (westSort xs) a₁ b := ⟨hba₁, before_of_adj hadj₁⟩
  have hinv_xs : ∃ a, IsInv xs a b := ⟨a₁, westSort_weakBruhat_self hnd a₁ b hab₁_S⟩
  have hrv_xs : IsRightValley xs b := rightValley_of_isDesBot_westSort hnd hdes_S
  rw [isDesBot_iff_invSet hnd_SB]
  by_cases ha1_SB : IsInv (westSort (bubblePass xs)) a₁ b
  · -- Case 1: `a₁` remains inverted with `b` in `S(B(xs))` -> witness `w = a₁`!
    refine ⟨a₁, ha1_SB, ?_⟩
    intro z hzb ha1z_SB
    have ha1z_S : IsInv (westSort xs) a₁ z :=
      westSort_bubblePass_weakBruhat_westSort hnd a₁ z ha1z_SB
    have hbz_S : IsInv (westSort xs) b z := by
      have hz_S : z ∈ westSort xs := mem_of_before_right ha1z_S.2
      have hb_S : b ∈ westSort xs := mem_of_before_right (before_of_adj hadj₁)
      rcases before_or_before hb_S hz_S (by omega) with h1 | h2
      · exact ⟨hzb, h1⟩
      · exfalso
        exact ((adj_iff_before_no_between hnd_S).mp hadj₁).2 z ⟨ha1z_S.2, h2⟩
    exact rightValley_transfer_west hnd hdes_S hinv_xs hbz_S
  · -- Case 2: `¬ IsInv (S(B(xs))) a₁ b`, so `a₂ < a₁` and `a₂ = max_{S(xs)}(< a₁)` -> witness `w = a₂`!
    have ha2_SB : IsInv (westSort (bubblePass xs)) a₂ b :=
      bubble_west_weakBruhat_west_bubble hnd a₂ b ⟨hba₂, before_of_adj hadj₂⟩
    have ⟨ha2_lt_a1, ha2_max⟩ : a₂ < a₁ ∧ ∀ x, Before (westSort xs) x a₁ → x ≤ a₂ := by
      rcases hcase with rfl | h2
      · exact absurd ha2_SB ha1_SB
      · exact h2
    refine ⟨a₂, ha2_SB, ?_⟩
    intro z hzb ha2z_SB
    have hb_SB : b ∈ westSort (bubblePass xs) := mem_of_before_right ha2_SB.2
    have hz_SB : z ∈ westSort (bubblePass xs) := mem_of_before_right ha2z_SB.2
    rcases before_or_before hb_SB hz_SB (by omega) with hbz | hzb_SB
    · exact ⟨hzb, hbz⟩
    · exfalso
      -- `z < b` precedes `b` in `S(B(xs))`, so `¬ IsInv (S(xs)) b z`, hence `Before (S(xs)) z a₁` and `Before xs z b`!
      have hnot_bz_S : ¬ IsInv (westSort xs) b z := fun h =>
        before_asymm hnd_SB hzb_SB (rightValley_transfer_west hnd hdes_S hinv_xs h).2
      have hb_S : b ∈ westSort xs := mem_of_before_right (before_of_adj hadj₁)
      have hz_S : z ∈ westSort xs :=
        (westSort_perm xs).mem_iff.mpr ((bubblePass_perm xs).mem_iff.mp ((westSort_perm _).mem_iff.mp hz_SB))
      have hzb_S : Before (westSort xs) z b := by
        rcases before_or_before hz_S hb_S (by omega) with h | h
        · exact h
        · exact absurd ⟨hzb, h⟩ hnot_bz_S
      have ha1_S : a₁ ∈ westSort xs := mem_of_before_left (before_of_adj hadj₁)
      have hza1_S : Before (westSort xs) z a₁ := by
        rcases before_or_before hz_S ha1_S (by omega) with h | h
        · exact h
        · exact absurd ⟨h, hzb_S⟩ (((adj_iff_before_no_between hnd_S).mp hadj₁).2 z)
      have hb_xs : b ∈ xs := (westSort_perm xs).mem_iff.mp hb_S
      have hz_xs : z ∈ xs := (westSort_perm xs).mem_iff.mp hz_S
      have hzb_xs : Before xs z b := by
        rcases before_or_before hz_xs hb_xs (by omega) with h | h
        · exact h
        · exact absurd (inv_rightValley_westSort hnd hrv_xs ⟨hzb, h⟩) hnot_bz_S
      -- From `IsInv (S(B(xs))) a₂ z`, get `c > a₂` between `a₂` and `z` in `B(xs)`, then `d > c` before `z` in `xs`!
      obtain ⟨_, c, ha2c, _, hcz_B⟩ := (invSet_westSort_iff hnd_B a₂ z).mp ha2z_SB
      obtain ⟨hcz_xs, d, hcd, hdz_xs⟩ :=
        (invSet_bubblePass_iff hnd c z).mp ⟨by omega, hcz_B⟩
      have hcb_xs : Before xs c b := before_trans hnd hcz_xs.2 hzb_xs
      have hdb_xs : Before xs d b := before_trans hnd hdz_xs.2 hzb_xs
      -- Also unpack `hab₁_S`: `Before xs a₁ b` and `∃ e > a₁, Before xs a₁ e ∧ Before xs e b`.
      obtain ⟨hab₁_xs, e, ha1e, ha1e_b, heb_b⟩ := (invSet_westSort_iff hnd a₁ b).mp hab₁_S
      have ha1_xs : a₁ ∈ xs := mem_of_before_left hab₁_xs.2
      have hd_xs : d ∈ xs := mem_of_before_left hdz_xs.2
      have he_xs : e ∈ xs := mem_of_before_left heb_b
      -- Helper: any `x > a₂` with `x < a₁` cannot satisfy `IsInv (S(xs)) x b`!
      have hno_between : ∀ x, a₂ < x → x < a₁ → ¬ IsInv (westSort xs) x b := by
        intro x hax hxa1 hxb_S
        have hx_S : x ∈ westSort xs := mem_of_before_left hxb_S.2
        have hxa1_S : Before (westSort xs) x a₁ := by
          rcases before_or_before hx_S ha1_S (by omega) with h | h
          · exact h
          · exact absurd ⟨h, hxb_S.2⟩ (((adj_iff_before_no_between hnd_S).mp hadj₁).2 x)
        have := ha2_max x hxa1_S; omega
      -- Now split on `d` vs `a₁`:
      by_cases hda1_gt : a₁ < d
      · rcases before_or_before ha1_xs hd_xs (by omega) with ha1d | hda1
        · -- `d > a₁` lies between `a₁` and `z` -> `IsInv (S(xs)) a₁ z`, contradicting `Before (S(xs)) z a₁`!
          have ha1z_S : IsInv (westSort xs) a₁ z :=
            (invSet_westSort_iff hnd a₁ z).mpr ⟨⟨by omega, before_trans hnd ha1d hdz_xs.2⟩, d, hda1_gt, ha1d, hdz_xs.2⟩
          exact before_asymm hnd_S hza1_S ha1z_S.2
        · -- `d > a₁` precedes `a₁` in `xs` -> `IsInv (S(B(xs))) a₁ b`, contradicting `ha1_SB`!
          exact ha1_SB (inv_west_bubble_of_gt_before_left hnd hab₁_S hda1_gt hda1)
      · by_cases hda1_eq : d = a₁
        · -- `d = a₁`, so `Before xs a₁ z` and `a₂ < c < a₁`:
          have ha1z_xs : Before xs a₁ z := hda1_eq ▸ hdz_xs.2
          rcases before_or_before he_xs hz_xs (by omega) with hez | hze
          · have ha1z_S : IsInv (westSort xs) a₁ z :=
              (invSet_westSort_iff hnd a₁ z).mpr ⟨⟨by omega, ha1z_xs⟩, e, ha1e, ha1e_b, hez⟩
            exact before_asymm hnd_S hza1_S ha1z_S.2
          · have hcb_S : IsInv (westSort xs) c b :=
              (invSet_westSort_iff hnd c b).mpr
                ⟨⟨by omega, hcb_xs⟩, e, by omega, before_trans hnd hcz_xs.2 hze, heb_b⟩
            exact hno_between c ha2c (by omega) hcb_S
        · -- `a₂ < c < d < a₁`:
          have hda1_lt : d < a₁ := by omega
          rcases before_or_before ha1_xs hz_xs (by omega) with ha1z_xs | hza1_xs
          · rcases before_or_before he_xs hz_xs (by omega) with hez | hze
            · have ha1z_S : IsInv (westSort xs) a₁ z :=
                (invSet_westSort_iff hnd a₁ z).mpr ⟨⟨by omega, ha1z_xs⟩, e, ha1e, ha1e_b, hez⟩
              exact before_asymm hnd_S hza1_S ha1z_S.2
            · have hdb_S : IsInv (westSort xs) d b :=
                (invSet_westSort_iff hnd d b).mpr
                  ⟨⟨by omega, hdb_xs⟩, e, by omega, before_trans hnd hdz_xs.2 hze, heb_b⟩
              exact hno_between d (Nat.lt_trans ha2c hcd) hda1_lt hdb_S
          · have hdb_S : IsInv (westSort xs) d b :=
              (invSet_westSort_iff hnd d b).mpr
                ⟨⟨by omega, hdb_xs⟩, a₁, hda1_lt, before_trans hnd hdz_xs.2 hza1_xs, hab₁_xs.2⟩
            exact hno_between d (Nat.lt_trans ha2c hcd) hda1_lt hdb_S

/-- **Main Descent-Bottom Commutator 2 (`desBot_bubble_pop_sub_pop_bubble`):**
`DesBot(B(P(xs))) ⊆ DesBot(P(B(xs)))` for every duplicate-free list `xs`. -/
theorem desBot_bubble_pop_sub_pop_bubble {xs : List Nat} (hnd : xs.Nodup) :
    DesBotSub (bubblePass (popSort xs)) (popSort (bubblePass xs)) := by
  have hnd_P : (popSort xs).Nodup := ((popSort_perm xs).nodup_iff).mpr hnd
  have hnd_B : (bubblePass xs).Nodup := ((bubblePass_perm xs).nodup_iff).mpr hnd
  have hnd_PB : (popSort (bubblePass xs)).Nodup := ((popSort_perm _).nodup_iff).mpr hnd_B
  intro b hdes_BP
  obtain ⟨a₁, a₂, hba₁, hadj₁, hba₂, hadj₂, hcase⟩ := desBot_bubblePass_witnesses hnd_P hdes_BP
  have hdes_P : IsDesBot (popSort xs) b := ⟨a₁, hba₁, hadj₁⟩
  have hab₁_P : IsInv (popSort xs) a₁ b := ⟨hba₁, before_of_adj hadj₁⟩
  have hinv_xs : ∃ a, IsInv xs a b := ⟨a₁, popSort_weakBruhat_self hnd a₁ b hab₁_P⟩
  have hrv_xs : IsRightValley xs b := rightValley_of_isDesBot_popSort hnd hdes_P
  rw [isDesBot_iff_invSet hnd_PB]
  by_cases ha1_PB : IsInv (popSort (bubblePass xs)) a₁ b
  · -- Case 1: `a₁` remains inverted with `b` in `P(B(xs))` -> witness `w = a₁`!
    refine ⟨a₁, ha1_PB, ?_⟩
    intro z hzb ha1z_PB
    have ha1z_P : IsInv (popSort xs) a₁ z :=
      popSort_bubblePass_weakBruhat_popSort hnd a₁ z ha1z_PB
    have hbz_P : IsInv (popSort xs) b z := by
      have hz_P : z ∈ popSort xs := mem_of_before_right ha1z_P.2
      have hb_P : b ∈ popSort xs := mem_of_before_right (before_of_adj hadj₁)
      rcases before_or_before hb_P hz_P (by omega) with h1 | h2
      · exact ⟨hzb, h1⟩
      · exfalso
        exact ((adj_iff_before_no_between hnd_P).mp hadj₁).2 z ⟨ha1z_P.2, h2⟩
    exact rightValley_transfer_pop hnd hdes_P hinv_xs hbz_P
  · -- Case 2: `a₂ < a₁` and `a₂ = max_{P(xs)}(< a₁)` -> witness `w = a₂`!
    have ha2_PB : IsInv (popSort (bubblePass xs)) a₂ b :=
      bubble_pop_weakBruhat_pop_bubble hnd a₂ b ⟨hba₂, before_of_adj hadj₂⟩
    have ⟨ha2_lt_a1, ha2_max⟩ : a₂ < a₁ ∧ ∀ x, Before (popSort xs) x a₁ → x ≤ a₂ := by
      rcases hcase with rfl | h2
      · exact absurd ha2_PB ha1_PB
      · exact h2
    refine ⟨a₂, ha2_PB, ?_⟩
    intro z hzb ha2z_PB
    have hb_PB : b ∈ popSort (bubblePass xs) := mem_of_before_right ha2_PB.2
    have hz_PB : z ∈ popSort (bubblePass xs) := mem_of_before_right ha2z_PB.2
    rcases before_or_before hb_PB hz_PB (by omega) with hbz | hzb_PB
    · exact ⟨hzb, hbz⟩
    · exfalso
      -- `z < b` precedes `b` in `P(B(xs))`, so `Before (P(xs)) z a₁` and `Before xs z b`:
      have hnot_bz_P : ¬ IsInv (popSort xs) b z := fun h =>
        before_asymm hnd_PB hzb_PB (rightValley_transfer_pop hnd hdes_P hinv_xs h).2
      have hb_P : b ∈ popSort xs := mem_of_before_right (before_of_adj hadj₁)
      have hz_P : z ∈ popSort xs :=
        (popSort_perm xs).mem_iff.mpr ((bubblePass_perm xs).mem_iff.mp ((popSort_perm _).mem_iff.mp hz_PB))
      have hzb_P : Before (popSort xs) z b := by
        rcases before_or_before hz_P hb_P (by omega) with h | h
        · exact h
        · exact absurd ⟨hzb, h⟩ hnot_bz_P
      have ha1_P : a₁ ∈ popSort xs := mem_of_before_left (before_of_adj hadj₁)
      have hza1_P : Before (popSort xs) z a₁ := by
        rcases before_or_before hz_P ha1_P (by omega) with h | h
        · exact h
        · exact absurd ⟨h, hzb_P⟩ (((adj_iff_before_no_between hnd_P).mp hadj₁).2 z)
      have hb_xs : b ∈ xs := (popSort_perm xs).mem_iff.mp hb_P
      have hz_xs : z ∈ xs := (popSort_perm xs).mem_iff.mp hz_P
      have hzb_xs : Before xs z b := by
        rcases before_or_before hz_xs hb_xs (by omega) with h | h
        · exact h
        · exact absurd (inv_rightValley_popSort hnd hrv_xs ⟨hzb, h⟩) hnot_bz_P
      -- Unpack `IsInv (P(B(xs))) a₂ z`:
      obtain ⟨ha2z_B, hasc_a2z_B⟩ := (invSet_popSort_iff hnd_B a₂ z).mp ha2z_PB
      obtain ⟨ha2z_xs, x₁, ha2x₁, hx₁z_xs⟩ := (invSet_bubblePass_iff hnd a₂ z).mp ha2z_B
      obtain ⟨_, hasc_a2z_xs⟩ := (invSet_popSort_iff hnd a₂ z).mp
        (popSort_bubblePass_weakBruhat_popSort hnd a₂ z ha2z_PB)
      -- Claim 1: every `x > a₂` with `Before xs x z` satisfies `¬ HasAscentBetween xs x z`.
      have hclaim1 : ∀ x, a₂ < x → Before xs x z → ¬ HasAscentBetween xs x z := by
        intro x hax hxz hasc_xz
        have hxz_P : IsInv (popSort xs) x z := (invSet_popSort_iff hnd x z).mpr ⟨⟨by omega, hxz⟩, hasc_xz⟩
        have hxa1_P : Before (popSort xs) x a₁ := before_trans hnd_P hxz_P.2 hza1_P
        have := ha2_max x hxa1_P; omega
      -- Claim 2: `x₁` is the UNIQUE element `> a₂` preceding `z` in `xs`!
      have hclaim2 : ∀ x, a₂ < x → Before xs x z → x = x₁ := by
        intro x hax hxz
        by_cases hxeq : x = x₁
        · exact hxeq
        · exfalso
          have hasc_zb : HasAscentBetween xs z b := hasAscentBetween_of_lt hnd hzb hzb_xs
          have hxb_P : IsInv (popSort xs) x b :=
            (invSet_popSort_iff hnd x b).mpr
              ⟨⟨by omega, before_trans hnd hxz hzb_xs⟩, hasAscentBetween_extend_left hnd hxz hasc_zb⟩
          have hx₁b_P : IsInv (popSort xs) x₁ b :=
            (invSet_popSort_iff hnd x₁ b).mpr
              ⟨⟨by omega, before_trans hnd hx₁z_xs.2 hzb_xs⟩, hasAscentBetween_extend_left hnd hx₁z_xs.2 hasc_zb⟩
          -- At least one of `x, x₁` is `≠ a₁`, hence precedes `a₁` in `P(xs)`, contradicting `ha2_max`!
          have hcontra : ∀ w, a₂ < w → w ≠ a₁ → Before (popSort xs) w b → False := by
            intro w haw hwa1 hwb_P
            have hw_P : w ∈ popSort xs := mem_of_before_left hwb_P
            have hwa1_P : Before (popSort xs) w a₁ := by
              rcases before_or_before hw_P ha1_P hwa1 with h | h
              · exact h
              · exact absurd ⟨h, hwb_P⟩ (((adj_iff_before_no_between hnd_P).mp hadj₁).2 w)
            have := ha2_max w hwa1_P; omega
          by_cases hxa1 : x = a₁
          · exact hcontra x₁ ha2x₁ (by omega) hx₁b_P.2
          · exact hcontra x hax hxa1 hxb_P.2
      -- Claim 3: `Before xs a₂ x₁`, `listMax` entering `x₁` is `a₂`, and `x₁ .. z` is `StrictlyDec`!
      have ha2x₁_bef : Before xs a₂ x₁ := by
        have ha2_xs : a₂ ∈ xs := mem_of_before_left ha2z_xs.2
        have hx1_xs : x₁ ∈ xs := mem_of_before_left hx₁z_xs.2
        rcases before_or_before ha2_xs hx1_xs (by omega) with h | h
        · exact h
        · exfalso
          exact hclaim1 x₁ ha2x₁ hx₁z_xs.2 (hasAscentBetween_extend_left hnd h hasc_a2z_xs)
      -- Split `xs = p₁ ++ x₁ :: seg ++ z :: p₃` using `Before xs x₁ z`:
      rcases hx₁z_xs.2 with ⟨p₁, seg, p₃, hxs_eq⟩
      have hnd_eq : (p₁ ++ x₁ :: seg ++ z :: p₃).Nodup := hxs_eq ▸ hnd
      have hsd_x1z : StrictlyDec (x₁ :: seg ++ [z]) := by
        have hnot_asc := hclaim1 x₁ ha2x₁ (hxs_eq ▸ ⟨p₁, seg, p₃, rfl⟩)
        rw [hxs_eq, hasAscentBetween_iff_not_strictlyDec hnd_eq] at hnot_asc
        -- `¬ ¬ StrictlyDec` is decidable on finite lists? Wait: prove `StrictlyDec` directly from `hnot_asc`!
        apply strictlyDec_of_no_adj_ascent
        · have h1 : (x₁ :: seg ++ z :: p₃).Nodup :=
            (List.nodup_append.mp (by simpa [List.append_assoc] using hnd_eq)).2.1
          have h2 : ((x₁ :: seg ++ [z]) ++ p₃).Nodup := by simpa [List.append_assoc] using h1
          exact (List.nodup_append.mp h2).1
        · intro u v hadj huv
          exact hnot_asc (fun h => strictlyDec_no_adj_ascent h hadj huv)
      -- `a₂ ∈ p₁`, so `p₁ = h0 :: p1'`, and every element of `p₁` is `≤ a₂`:
      have ha2_p1 : a₂ ∈ p₁ := by
        have hnd1 : (p₁ ++ x₁ :: (seg ++ z :: p₃)).Nodup := by simpa [List.append_assoc] using hnd_eq
        exact mem_pref_of_before hnd1 (by simpa [List.append_assoc, hxs_eq] using ha2x₁_bef)
      have hp1_le : ∀ w ∈ p₁, w ≤ a₂ := by
        intro w hw
        by_cases hgt : a₂ < w
        · exfalso
          have hwz : Before xs w z := by
            rw [hxs_eq]
            obtain ⟨q₁, q₂, rfl⟩ := List.append_of_mem hw
            exact ⟨q₁, q₂ ++ x₁ :: seg, p₃, by simp [List.append_assoc]⟩
          have hwx1 : w = x₁ := hclaim2 w hgt hwz
          subst hwx1
          have hnd1 : (p₁ ++ w :: (seg ++ z :: p₃)).Nodup := by simpa [List.append_assoc] using hnd_eq
          exact (List.nodup_append.mp hnd1).2.2 w hw w List.mem_cons_self rfl
        · omega
      cases p₁ with
      | nil => simp at ha2_p1
      | cons h0 p1' =>
          have hm_eq : listMax h0 p1' = a₂ := by
            have hle1 : a₂ ≤ listMax h0 p1' := by
              simp only [List.mem_cons] at ha2_p1
              rcases ha2_p1 with rfl | ha2'
              · exact le_listMax a₂ p1'
              · exact mem_le_listMax h0 ha2'
            have hle2 : listMax h0 p1' ≤ a₂ := hp1_le (listMax h0 p1') (listMax_mem h0 p1')
            omega
          -- Every element of `seg ++ [z]` is `< a₂` (by `hclaim2` + `Nodup`)!
          have hseg_lt : ∀ w ∈ seg ++ [z], w < a₂ := by
            intro w hw
            simp only [List.mem_append, List.mem_singleton] at hw
            rcases hw with hw_seg | rfl
            · have hne_a2 : w ≠ a₂ := by
                intro hweq; subst hweq
                have hnd1 : ((h0 :: p1') ++ x₁ :: (seg ++ z :: p₃)).Nodup :=
                  (by simp [List.append_assoc] : (h0 :: p1') ++ x₁ :: seg ++ z :: p₃ = (h0 :: p1') ++ x₁ :: (seg ++ z :: p₃)) ▸ hnd_eq
                exact (List.nodup_append.mp hnd1).2.2 w ha2_p1 w (by simp [hw_seg]) rfl
              have hne_x1 : w ≠ x₁ := by
                have hnd1 : ((h0 :: p1') ++ x₁ :: (seg ++ z :: p₃)).Nodup :=
                  (by simp [List.append_assoc] : (h0 :: p1') ++ x₁ :: seg ++ z :: p₃ = (h0 :: p1') ++ x₁ :: (seg ++ z :: p₃)) ▸ hnd_eq
                have hnd2 : (x₁ :: (seg ++ z :: p₃)).Nodup := (List.nodup_append.mp hnd1).2.1
                intro hweq; subst hweq
                exact (List.nodup_cons.mp hnd2).1 (by simp [hw_seg])
              by_cases hgt : a₂ < w
              · exfalso
                obtain ⟨q₁, q₂, rfl⟩ := List.append_of_mem hw_seg
                have hwz : Before xs w z := by
                  rw [hxs_eq]; exact ⟨(h0 :: p1') ++ [x₁] ++ q₁, q₂, p₃, by simp [List.append_assoc]⟩
                exact hne_x1 (hclaim2 w hgt hwz)
              · omega
            · omega
          -- Now `bubblePass xs` emits `out ++ a₂ :: seg ++ z :: bubbleCarry x₁ p₃`!
          obtain ⟨out, heq_bc, _⟩ := bubbleCarry_append h0 p1' (x₁ :: seg ++ z :: p₃)
          have hbp_eq : bubblePass xs = out ++ a₂ :: seg ++ z :: bubbleCarry x₁ p₃ := by
            rw [hxs_eq]
            have h1 : bubblePass ((h0 :: p1') ++ x₁ :: seg ++ z :: p₃) =
                out ++ bubbleCarry (listMax h0 p1') (x₁ :: seg ++ z :: p₃) := by
              simpa [bubblePass, List.append_assoc] using heq_bc
            rw [h1, hm_eq]
            have hnot_gt : ¬ (a₂ > x₁) := by omega
            simp only [List.cons_append, bubbleCarry, hnot_gt, ↓reduceIte]
            cases seg with
            | nil =>
                have hxz : x₁ > z := by omega
                simp only [List.nil_append, bubbleCarry, hxz, ↓reduceIte, List.append_assoc, List.cons_append]
            | cons y seg' =>
                have hyx1 : y < x₁ := hsd_x1z.1
                have hcarry := bubbleCarry_strictlyDec x₁ y seg' p₃ z hyx1 hsd_x1z.2
                rw [hcarry]; simp [List.append_assoc]
          -- And `a₂ :: seg ++ [z]` is `StrictlyDec`, contradicting `hasc_a2z_B`!
          have hsd_a2z : StrictlyDec (a₂ :: seg ++ [z]) := by
            cases seg with
            | nil => exact ⟨by omega, trivial⟩
            | cons y seg' => exact ⟨hseg_lt y (by simp), hsd_x1z.2⟩
          rw [hbp_eq] at hnd_B hasc_a2z_B
          exact (hasAscentBetween_iff_not_strictlyDec hnd_B).mp hasc_a2z_B hsd_a2z

end OneStepCommutators

section IteratedAndCorollaries

/-- **Iterated Bubble–West Commutator (`iterBubble_west_commutator`):**
For every `k : Nat` and every duplicate-free list `xs`,
`B^k(S(xs)) ⪯_B S(B^k(xs))` (simultaneous Right Weak Bruhat and Descent-Bottom inclusion). -/
theorem iterBubble_west_commutator (k : Nat) {xs : List Nat} (hnd : xs.Nodup) :
    BubbleLe (iterBubble k (westSort xs)) (westSort (iterBubble k xs)) := by
  induction k with
  | zero => exact bubbleLe_refl (westSort xs)
  | succ k ih =>
      simp only [iterBubble]
      have hperm1 : (iterBubble k (westSort xs)).Perm (westSort (iterBubble k xs)) :=
        ((iterBubble_perm k (westSort xs)).trans (westSort_perm xs)).trans
          ((westSort_perm (iterBubble k xs)).trans (iterBubble_perm k xs)).symm
      have hnd1 : (iterBubble k (westSort xs)).Nodup :=
        (((iterBubble_perm k _).trans (westSort_perm xs)).nodup_iff).mpr hnd
      have hnd_Bk : (iterBubble k xs).Nodup := ((iterBubble_perm k xs).nodup_iff).mpr hnd
      have hstep1 : BubbleLe (bubblePass (iterBubble k (westSort xs)))
          (bubblePass (westSort (iterBubble k xs))) :=
        bubbleOrder_bubblePass_mono hperm1 hnd1 ih
      have hstep2 : BubbleLe (bubblePass (westSort (iterBubble k xs)))
          (westSort (bubblePass (iterBubble k xs))) :=
        ⟨bubble_west_weakBruhat_west_bubble hnd_Bk, desBot_bubble_west_sub_west_bubble hnd_Bk⟩
      exact bubbleLe_trans hstep1 hstep2

/-- **Iterated Bubble–Pop Commutator (`iterBubble_pop_commutator`):**
For every `k : Nat` and every duplicate-free list `xs`,
`B^k(P(xs)) ⪯_B P(B^k(xs))` (simultaneous Right Weak Bruhat and Descent-Bottom inclusion). -/
theorem iterBubble_pop_commutator (k : Nat) {xs : List Nat} (hnd : xs.Nodup) :
    BubbleLe (iterBubble k (popSort xs)) (popSort (iterBubble k xs)) := by
  induction k with
  | zero => exact bubbleLe_refl (popSort xs)
  | succ k ih =>
      simp only [iterBubble]
      have hperm1 : (iterBubble k (popSort xs)).Perm (popSort (iterBubble k xs)) :=
        ((iterBubble_perm k (popSort xs)).trans (popSort_perm xs)).trans
          ((popSort_perm (iterBubble k xs)).trans (iterBubble_perm k xs)).symm
      have hnd1 : (iterBubble k (popSort xs)).Nodup :=
        (((iterBubble_perm k _).trans (popSort_perm xs)).nodup_iff).mpr hnd
      have hnd_Bk : (iterBubble k xs).Nodup := ((iterBubble_perm k xs).nodup_iff).mpr hnd
      have hstep1 : BubbleLe (bubblePass (iterBubble k (popSort xs)))
          (bubblePass (popSort (iterBubble k xs))) :=
        bubbleOrder_bubblePass_mono hperm1 hnd1 ih
      have hstep2 : BubbleLe (bubblePass (popSort (iterBubble k xs)))
          (popSort (bubblePass (iterBubble k xs))) :=
        ⟨bubble_pop_weakBruhat_pop_bubble hnd_Bk, desBot_bubble_pop_sub_pop_bubble hnd_Bk⟩
      exact bubbleLe_trans hstep1 hstep2

/-- Inversion-count commutator inequality `invCnt(B^k(S(xs))) ≤ invCnt(S(B^k(xs)))`. -/
theorem invCnt_iterBubble_west_le (k : Nat) {xs : List Nat} (hnd : xs.Nodup) :
    invCnt (iterBubble k (westSort xs)) ≤ invCnt (westSort (iterBubble k xs)) := by
  have hperm : (iterBubble k (westSort xs)).Perm (westSort (iterBubble k xs)) :=
    ((iterBubble_perm k (westSort xs)).trans (westSort_perm xs)).trans
      ((westSort_perm (iterBubble k xs)).trans (iterBubble_perm k xs)).symm
  have hnd1 : (iterBubble k (westSort xs)).Nodup :=
    (((iterBubble_perm k _).trans (westSort_perm xs)).nodup_iff).mpr hnd
  exact invCnt_le_of_weakBruhatLe hperm hnd1 (iterBubble_west_commutator k hnd).1

/-- Descent-count commutator inequality `desCnt(B^k(S(xs))) ≤ desCnt(S(B^k(xs)))`. -/
theorem desCnt_iterBubble_west_le (k : Nat) {xs : List Nat} (hnd : xs.Nodup) :
    desCnt (iterBubble k (westSort xs)) ≤ desCnt (westSort (iterBubble k xs)) := by
  have hperm : (iterBubble k (westSort xs)).Perm (westSort (iterBubble k xs)) :=
    ((iterBubble_perm k (westSort xs)).trans (westSort_perm xs)).trans
      ((westSort_perm (iterBubble k xs)).trans (iterBubble_perm k xs)).symm
  have hnd1 : (iterBubble k (westSort xs)).Nodup :=
    (((iterBubble_perm k _).trans (westSort_perm xs)).nodup_iff).mpr hnd
  exact desCnt_le_of_desBotSub hperm hnd1 (iterBubble_west_commutator k hnd).2

/-- Inversion-count commutator inequality `invCnt(B^k(P(xs))) ≤ invCnt(P(B^k(xs)))`. -/
theorem invCnt_iterBubble_pop_le (k : Nat) {xs : List Nat} (hnd : xs.Nodup) :
    invCnt (iterBubble k (popSort xs)) ≤ invCnt (popSort (iterBubble k xs)) := by
  have hperm : (iterBubble k (popSort xs)).Perm (popSort (iterBubble k xs)) :=
    ((iterBubble_perm k (popSort xs)).trans (popSort_perm xs)).trans
      ((popSort_perm (iterBubble k xs)).trans (iterBubble_perm k xs)).symm
  have hnd1 : (iterBubble k (popSort xs)).Nodup :=
    (((iterBubble_perm k _).trans (popSort_perm xs)).nodup_iff).mpr hnd
  exact invCnt_le_of_weakBruhatLe hperm hnd1 (iterBubble_pop_commutator k hnd).1

/-- Descent-count commutator inequality `desCnt(B^k(P(xs))) ≤ desCnt(P(B^k(xs)))`. -/
theorem desCnt_iterBubble_pop_le (k : Nat) {xs : List Nat} (hnd : xs.Nodup) :
    desCnt (iterBubble k (popSort xs)) ≤ desCnt (popSort (iterBubble k xs)) := by
  have hperm : (iterBubble k (popSort xs)).Perm (popSort (iterBubble k xs)) :=
    ((iterBubble_perm k (popSort xs)).trans (popSort_perm xs)).trans
      ((popSort_perm (iterBubble k xs)).trans (iterBubble_perm k xs)).symm
  have hnd1 : (iterBubble k (popSort xs)).Nodup :=
    (((iterBubble_perm k _).trans (popSort_perm xs)).nodup_iff).mpr hnd
  exact desCnt_le_of_desBotSub hperm hnd1 (iterBubble_pop_commutator k hnd).2

end IteratedAndCorollaries

section SeparationWitnesses

/-- **Sharpness 1 (`exists_westSort_popSort_not_weakBruhat_mono`):**
Unlike `bubblePass`, neither `westSort` nor `popSort` is monotone in Right Weak Bruhat Order:
`u = [0, 1, 3, 4, 2] ≤_R [0, 1, 4, 3, 2] = v`, yet `S(u) ≰_R S(v)` and `P(u) ≰_R P(v)`. -/
theorem exists_westSort_popSort_not_weakBruhat_mono :
    ∃ u v : List Nat,
      u.Perm v ∧ u.Nodup ∧ WeakBruhatLe u v ∧
      ¬ WeakBruhatLe (westSort u) (westSort v) ∧
      ¬ WeakBruhatLe (popSort u) (popSort v) := by
  refine ⟨[0, 1, 3, 4, 2], [0, 1, 4, 3, 2], ?_, by decide, ?_, ?_, ?_⟩
  · exact List.Perm.cons 0 (List.Perm.cons 1 (List.Perm.swap 4 3 [2]))
  · -- `InvSet [0, 1, 3, 4, 2] = {(3, 2), (4, 2)} ⊆ {(4, 3), (4, 2), (3, 2)} = InvSet [0, 1, 4, 3, 2]`:
    intro a b ⟨hba, l₁, l₂, l₃, heq⟩
    have ha : a ∈ [0, 1, 3, 4, 2] := by rw [heq]; simp
    have hb : b ∈ [0, 1, 3, 4, 2] := by rw [heq]; simp
    -- Exhaustively check `(a, b)` on the 5-element list:
    have hnd_u : ([0, 1, 3, 4, 2] : List Nat).Nodup := by decide
    have hnd_v : ([0, 1, 4, 3, 2] : List Nat).Nodup := by decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    first
    | omega
    | exact ⟨hba, [0, 1, 4], [], [], rfl⟩
    | exact ⟨hba, [0, 1], [3], [], rfl⟩
    | (exfalso; exact before_asymm hnd_u ⟨l₁, l₂, l₃, heq⟩ (by
        first
        | exact ⟨[], [], [3, 4, 2], rfl⟩
        | exact ⟨[], [1], [4, 2], rfl⟩
        | exact ⟨[], [1, 3], [2], rfl⟩
        | exact ⟨[], [1, 3, 4], [], rfl⟩
        | exact ⟨[0], [], [4, 2], rfl⟩
        | exact ⟨[0], [3], [2], rfl⟩
        | exact ⟨[0], [3, 4], [], rfl⟩
        | exact ⟨[0, 1], [], [2], rfl⟩))
  · -- `westSort [0, 1, 3, 4, 2] = [0, 1, 3, 2, 4]` has `(3, 2)`,
    -- `westSort [0, 1, 4, 3, 2] = [0, 1, 2, 3, 4]` does NOT!
    have hSu : westSort [0, 1, 3, 4, 2] = [0, 1, 3, 2, 4] := by
      simp [westSort, westRun]
    have hSv : westSort [0, 1, 4, 3, 2] = [0, 1, 2, 3, 4] := by
      simp [westSort, westRun]
    intro hle
    rw [hSu, hSv] at hle
    have h1 : IsInv [0, 1, 3, 2, 4] 3 2 := ⟨by omega, [0, 1], [], [4], by decide⟩
    have h2 : IsInv [0, 1, 2, 3, 4] 3 2 := hle 3 2 h1
    have hnd_Sv : ([0, 1, 2, 3, 4] : List Nat).Nodup := by decide
    have h23 : Before [0, 1, 2, 3, 4] 2 3 := ⟨[0, 1], [], [4], by decide⟩
    exact before_asymm hnd_Sv h2.2 h23
  · -- `popSort [0, 1, 3, 4, 2] = [0, 1, 3, 2, 4]` has `(3, 2)`,
    -- `popSort [0, 1, 4, 3, 2] = [0, 1, 2, 3, 4]` does NOT!
    intro hle
    have h1 : IsInv (popSort [0, 1, 3, 4, 2]) 3 2 := ⟨by omega, [0, 1], [], [4], by decide⟩
    have h2 : IsInv (popSort [0, 1, 4, 3, 2]) 3 2 := hle 3 2 h1
    have hnd_Pv : (popSort [0, 1, 4, 3, 2]).Nodup := by decide
    have h23 : Before (popSort [0, 1, 4, 3, 2]) 2 3 := ⟨[0, 1], [], [4], by decide⟩
    exact before_asymm hnd_Pv h2.2 h23

/-- **Sharpness 2 (`exists_bubble_pop_incomparable`):**
In contrast to `S(xs) ≤_R B(xs)` and `S(xs) ≤_R P(xs)`, the operators `B` and `P` are
incomparable in Right Weak Bruhat Order: at `xs = [3, 1, 2, 0]`, `B(xs) = [1, 2, 0, 3]` and
`P(xs) = [1, 3, 0, 2]` have neither `B(xs) ≤_R P(xs)` nor `P(xs) ≤_R B(xs)`. -/
theorem exists_bubble_pop_incomparable :
    ∃ xs : List Nat, xs.Nodup ∧
      ¬ WeakBruhatLe (bubblePass xs) (popSort xs) ∧
      ¬ WeakBruhatLe (popSort xs) (bubblePass xs) := by
  refine ⟨[3, 1, 2, 0], by decide, ?_, ?_⟩
  · intro hle
    have h1 : IsInv (bubblePass [3, 1, 2, 0]) 2 0 := ⟨by omega, [1], [], [3], by decide⟩
    have h2 : IsInv (popSort [3, 1, 2, 0]) 2 0 := hle 2 0 h1
    have hnd_P : (popSort [3, 1, 2, 0]).Nodup := by decide
    have h02 : Before (popSort [3, 1, 2, 0]) 0 2 := ⟨[1, 3], [], [], by decide⟩
    exact before_asymm hnd_P h2.2 h02
  · intro hle
    have h1 : IsInv (popSort [3, 1, 2, 0]) 3 0 := ⟨by omega, [1], [], [2], by decide⟩
    have h2 : IsInv (bubblePass [3, 1, 2, 0]) 3 0 := hle 3 0 h1
    have hnd_B : (bubblePass [3, 1, 2, 0]).Nodup := by decide
    have h03 : Before (bubblePass [3, 1, 2, 0]) 0 3 := ⟨[1, 2], [], [], by decide⟩
    exact before_asymm hnd_B h2.2 h03

end SeparationWitnesses

end WeakBruhatCommutators
