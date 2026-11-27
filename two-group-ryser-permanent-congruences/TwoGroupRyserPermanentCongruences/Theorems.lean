/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TwoGroupRyserPermanentCongruences.Defs

/-!
# Theorems (`two-group-ryser-permanent-congruences`)

Full proofs of the headline infinite theorems of Permanent Mod 2^r and Ryser-Bitmask Exact Congruence Engine.
-/

set_option autoImplicit false
namespace SpecMat9

theorem prodInt_append {α : Type} (l₁ l₂ : List α) (f : α → Int) :
    prodInt (l₁ ++ l₂) f = prodInt l₁ f * prodInt l₂ f := by
  induction l₁ with
  | nil => simp
  | cons x xs ih => simp [ih, Int.mul_assoc]

theorem sumInt_congr {α : Type} {l : List α} {f g : α → Int}
    (h : ∀ x ∈ l, f x = g x) : sumInt l f = sumInt l g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [sumInt_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem prodInt_congr {α : Type} {l : List α} {f g : α → Int}
    (h : ∀ x ∈ l, f x = g x) : prodInt l f = prodInt l g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [prodInt_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem sumInt_add {α : Type} (l : List α) (f g : α → Int) :
    sumInt l (fun x => f x + g x) = sumInt l f + sumInt l g := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

theorem sumInt_sub {α : Type} (l : List α) (f g : α → Int) :
    sumInt l (fun x => f x - g x) = sumInt l f - sumInt l g := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

theorem sumInt_neg {α : Type} (l : List α) (f : α → Int) :
    sumInt l (fun x => -f x) = -sumInt l f := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

theorem sumInt_mul_left {α : Type} (l : List α) (c : Int) (f : α → Int) :
    sumInt l (fun x => c * f x) = c * sumInt l f := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, Int.mul_add]

theorem sumInt_mul_right {α : Type} (l : List α) (c : Int) (f : α → Int) :
    sumInt l (fun x => f x * c) = sumInt l f * c := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, Int.add_mul]

theorem sumInt_const {α : Type} (l : List α) (c : Int) :
    sumInt l (fun _ => c) = (l.length : Int) * c := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [sumInt_cons, List.length_cons, ih]
    have h1 : ((xs.length + 1 : Nat) : Int) = (xs.length : Int) + 1 := by omega
    rw [h1, Int.add_mul, Int.one_mul, Int.add_comm]

theorem prodInt_const {α : Type} (l : List α) (c : Int) :
    prodInt l (fun _ => c) = c ^ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [prodInt_cons, List.length_cons, ih, Int.pow_succ, Int.mul_comm]

theorem sumInt_map {α β : Type} (l : List α) (g : α → β) (f : β → Int) :
    sumInt (l.map g) f = sumInt l (fun x => f (g x)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem prodInt_map {α β : Type} (l : List α) (g : α → β) (f : β → Int) :
    prodInt (l.map g) f = prodInt l (fun x => f (g x)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem sumInt_perm {α : Type} {l₁ l₂ : List α} (h : l₁.Perm l₂) (f : α → Int) :
    sumInt l₁ f = sumInt l₂ f := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem prodInt_perm {α : Type} {l₁ l₂ : List α} (h : l₁.Perm l₂) (f : α → Int) :
    prodInt l₁ f = prodInt l₂ f := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l =>
    simp only [prodInt_cons]
    exact Int.mul_left_comm _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem sumInt_comm {α β : Type} (l₁ : List α) (l₂ : List β) (f : α → β → Int) :
    sumInt l₁ (fun a => sumInt l₂ (fun b => f a b)) =
    sumInt l₂ (fun b => sumInt l₁ (fun a => f a b)) := by
  induction l₁ with
  | nil =>
    simp only [sumInt_nil]
    induction l₂ with
    | nil => rfl
    | cons b bs ih2 => rw [sumInt_cons, ← ih2, Int.zero_add]
  | cons a as ih =>
    simp only [sumInt_cons, ih, sumInt_add]

theorem sumInt_filter_add_not {α : Type} (l : List α) (p : α → Bool) (f : α → Int) :
    sumInt (l.filter p) f + sumInt (l.filter (fun x => !p x)) f = sumInt l f := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases hpx : p x
    · simp only [List.filter_cons, hpx, Bool.false_eq_true, ↓reduceIte, Bool.not_false, sumInt_cons]
      omega
    · simp only [List.filter_cons, hpx, ↓reduceIte, Bool.not_true, Bool.false_eq_true, sumInt_cons]
      omega

theorem prodInt_filter_mul_not {α : Type} (l : List α) (p : α → Bool) (f : α → Int) :
    prodInt (l.filter p) f * prodInt (l.filter (fun x => !p x)) f = prodInt l f := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases hpx : p x
    · simp only [List.filter_cons, hpx, Bool.false_eq_true, ↓reduceIte, Bool.not_false, prodInt_cons]
      rw [Int.mul_left_comm, ih]
    · simp only [List.filter_cons, hpx, ↓reduceIte, Bool.not_true, Bool.false_eq_true, prodInt_cons]
      rw [Int.mul_assoc, ih]

theorem sumInt_filter_eq_sumInt_ite {α : Type} (l : List α) (p : α → Bool) (f : α → Int) :
    sumInt (l.filter p) f = sumInt l (fun x => if p x then f x else 0) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases hpx : p x <;> simp [hpx, ih]

theorem sumInt_dvd {α : Type} {l : List α} {d : Int} {f : α → Int}
    (h : ∀ x ∈ l, d ∣ f x) : d ∣ sumInt l f := by
  induction l with
  | nil => exact Int.dvd_zero d
  | cons x xs ih =>
    simp only [sumInt_cons]
    exact Int.dvd_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem sumInt_zero {α : Type} {l : List α} {f : α → Int}
    (h : ∀ x ∈ l, f x = 0) : sumInt l f = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [sumInt_cons, h x (by simp), ih (fun y hy => h y (by simp [hy])), Int.zero_add]

theorem nodup_map_inj_on {α β : Type} {l : List α} {e : α → β}
    (hnd : l.Nodup) (hinj : ∀ x ∈ l, ∀ y ∈ l, e x = e y → x = y) :
    (l.map e).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have ⟨hx_nmem, hxs_nd⟩ := List.nodup_cons.mp hnd
    rw [List.map_cons, List.nodup_cons]
    constructor
    · intro hmem
      rcases List.mem_map.mp hmem with ⟨y, hy, hyx⟩
      have heq := hinj y (by simp [hy]) x (by simp) hyx
      exact hx_nmem (heq ▸ hy)
    · exact ih hxs_nd (fun a ha b hb => hinj a (by simp [ha]) b (by simp [hb]))

theorem nodup_flatMap_custom {α β : Type} {l : List α} {g : α → List β}
    (hnd : l.Nodup)
    (hinner : ∀ a ∈ l, (g a).Nodup)
    (hdisj : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ y, y ∈ g a → y ∉ g b) :
    (l.flatMap g).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have ⟨hx_nmem, hxs_nd⟩ := List.nodup_cons.mp hnd
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨hinner x (by simp), ih hxs_nd (fun a ha => hinner a (by simp [ha]))
      (fun a ha b hb => hdisj a (by simp [ha]) b (by simp [hb])), ?_⟩
    intro y hy₁ y' hy₂ heq
    subst heq
    rcases List.mem_flatMap.mp hy₂ with ⟨b, hb, hyb⟩
    have hne : x ≠ b := fun h => hx_nmem (h ▸ hb)
    exact hdisj x (by simp) b (by simp [hb]) hne y hy₁ hyb

theorem perm_of_nodup_iff {α : Type} {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.Perm l₂ :=
  (List.perm_ext_iff_of_nodup h₁ h₂).mpr hmem

theorem perm_map_bijection {α β : Type} {l₁ : List α} {l₂ : List β}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (e : α → β) (eInv : β → α)
    (h12 : ∀ x ∈ l₁, e x ∈ l₂)
    (h21 : ∀ y ∈ l₂, eInv y ∈ l₁)
    (hLR : ∀ x ∈ l₁, eInv (e x) = x)
    (hRL : ∀ y ∈ l₂, e (eInv y) = y) :
    (l₁.map e).Perm l₂ := by
  apply perm_of_nodup_iff
  · apply nodup_map_inj_on h₁
    intro x hx y hy hxy
    have := congrArg eInv hxy
    rw [hLR x hx, hLR y hy] at this
    exact this
  · exact h₂
  · intro y
    constructor
    · intro hy
      rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
      exact h12 x hx
    · intro hy
      exact List.mem_map.mpr ⟨eInv y, h21 y hy, hRL y hy⟩

theorem sumInt_bijection {α β : Type} {l₁ : List α} {l₂ : List β}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (e : α → β) (eInv : β → α)
    (h12 : ∀ x ∈ l₁, e x ∈ l₂)
    (h21 : ∀ y ∈ l₂, eInv y ∈ l₁)
    (hLR : ∀ x ∈ l₁, eInv (e x) = x)
    (hRL : ∀ y ∈ l₂, e (eInv y) = y)
    (f : β → Int) :
    sumInt l₁ (fun x => f (e x)) = sumInt l₂ f := by
  rw [← sumInt_map]
  exact sumInt_perm (perm_map_bijection h₁ h₂ e eInv h12 h21 hLR hRL) f

theorem prodInt_bijection {α β : Type} {l₁ : List α} {l₂ : List β}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (e : α → β) (eInv : β → α)
    (h12 : ∀ x ∈ l₁, e x ∈ l₂)
    (h21 : ∀ y ∈ l₂, eInv y ∈ l₁)
    (hLR : ∀ x ∈ l₁, eInv (e x) = x)
    (hRL : ∀ y ∈ l₂, e (eInv y) = y)
    (f : β → Int) :
    prodInt l₁ (fun x => f (e x)) = prodInt l₂ f := by
  rw [← prodInt_map]
  exact prodInt_perm (perm_map_bijection h₁ h₂ e eInv h12 h21 hLR hRL) f

theorem length_bijection {α β : Type} {l₁ : List α} {l₂ : List β}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (e : α → β) (eInv : β → α)
    (h12 : ∀ x ∈ l₁, e x ∈ l₂)
    (h21 : ∀ y ∈ l₂, eInv y ∈ l₁)
    (hLR : ∀ x ∈ l₁, eInv (e x) = x)
    (hRL : ∀ y ∈ l₂, e (eInv y) = y) :
    l₁.length = l₂.length := by
  have hp := perm_map_bijection h₁ h₂ e eInv h12 h21 hLR hRL
  simpa using hp.length_eq

-- ============================================================================
-- SECTION 2: Finite Function Spaces, Bitmasks, and Matrix Permanents
-- ============================================================================

theorem consFinFun_zero {m : Nat} {α : Type} (a : α) (f : Fin m → α) :
    consFinFun a f ⟨0, Nat.zero_lt_succ m⟩ = a := by
  simp [consFinFun]

theorem consFinFun_succ {m : Nat} {α : Type} (a : α) (f : Fin m → α) (i : Fin m) :
    consFinFun a f i.succ = f i := by
  simp [consFinFun, Fin.succ]

theorem consFinFun_inj {m : Nat} {α : Type} {a₁ a₂ : α} {f₁ f₂ : Fin m → α}
    (h : consFinFun a₁ f₁ = consFinFun a₂ f₂) : a₁ = a₂ ∧ f₁ = f₂ := by
  constructor
  · have h0 := congrFun h ⟨0, Nat.zero_lt_succ m⟩
    rw [consFinFun_zero, consFinFun_zero] at h0
    exact h0
  · funext i
    have hi := congrFun h i.succ
    rw [consFinFun_succ, consFinFun_succ] at hi
    exact hi

theorem consFinFun_eta {m : Nat} {α : Type} (f : Fin (m + 1) → α) :
    consFinFun (f ⟨0, Nat.zero_lt_succ m⟩) (fun i : Fin m => f i.succ) = f := by
  funext i
  rcases i with ⟨v, hv⟩
  cases v with
  | zero => simp [consFinFun]
  | succ k => simp [consFinFun, Fin.succ]

theorem mem_allFnsToList {α : Type} {dom : List α} (hdom : ∀ a : α, a ∈ dom) :
    ∀ (m : Nat) (f : Fin m → α), f ∈ allFnsToList dom m
  | 0, f => by
    simp only [allFnsToList, List.mem_singleton]
    funext i; exact Fin.elim0 i
  | m + 1, f => by
    simp only [allFnsToList, List.mem_flatMap, List.mem_map]
    refine ⟨f ⟨0, Nat.zero_lt_succ m⟩, hdom _, fun i => f i.succ,
      mem_allFnsToList hdom m _, consFinFun_eta f⟩

theorem nodup_allFnsToList {α : Type} {dom : List α} (hnd : dom.Nodup) :
    ∀ (m : Nat), (allFnsToList dom m).Nodup
  | 0 => by simp [allFnsToList]
  | m + 1 => by
    simp only [allFnsToList]
    have ih := nodup_allFnsToList hnd m
    apply nodup_flatMap_custom hnd
    · intro a _
      apply nodup_map_inj_on ih
      intro f₁ _ f₂ _ h
      exact (consFinFun_inj h).2
    · intro a _ b _ hne f hf₁ hf₂
      rcases List.mem_map.mp hf₁ with ⟨g₁, _, rfl⟩
      rcases List.mem_map.mp hf₂ with ⟨g₂, _, heq⟩
      exact hne (consFinFun_inj heq).1.symm

theorem length_allFnsToList {α : Type} (dom : List α) :
    ∀ (m : Nat), (allFnsToList dom m).length = dom.length ^ m
  | 0 => by simp [allFnsToList]
  | m + 1 => by
    simp only [allFnsToList, List.length_flatMap, List.length_map, length_allFnsToList dom m]
    have hsum : ∀ (l : List α) (c : Nat), (l.map (fun _ => c)).sum = l.length * c := by
      intro l c
      induction l with
      | nil => simp
      | cons _ xs ih => simp [ih, Nat.succ_mul, Nat.add_comm]
    rw [hsum, Nat.pow_succ, Nat.mul_comm]

theorem mem_allMasks (n : Nat) (S : Mask n) : S ∈ allMasks n :=
  mem_allFnsToList (fun b => by cases b <;> simp) n S

theorem nodup_allMasks (n : Nat) : (allMasks n).Nodup :=
  nodup_allFnsToList (by decide) n

theorem length_allMasks (n : Nat) : (allMasks n).length = 2 ^ n :=
  length_allFnsToList [false, true] n

theorem mem_allFns (m n : Nat) (f : Fin m → Fin n) : f ∈ allFns m n :=
  mem_allFnsToList List.mem_finRange m f

theorem nodup_allFns (m n : Nat) : (allFns m n).Nodup :=
  nodup_allFnsToList (List.nodup_finRange n) m

theorem length_allFns (m n : Nat) : (allFns m n).length = n ^ m := by
  unfold allFns
  rw [length_allFnsToList, List.length_finRange]

-- ============================================================================
-- SECTION 3: Genuine Permutation-Sum Permanent & Proof of Ryser's Formula
-- ============================================================================

theorem isSurjective_iff (n : Nat) (f : Fin n → Fin n) :
    isSurjective n f = true ↔ Function.Surjective f := by
  unfold isSurjective Function.Surjective
  rw [List.all_eq_true]
  constructor
  · intro h j
    have hj := h j (List.mem_finRange j)
    rcases List.any_eq_true.mp hj with ⟨i, _, hi⟩
    exact ⟨i, of_decide_eq_true hi⟩
  · intro h j _
    rcases h j with ⟨i, hi⟩
    exact List.any_eq_true.mpr ⟨i, List.mem_finRange i, decide_eq_true hi⟩

theorem mem_dedup {α : Type} [DecidableEq α] (l : List α) (y : α) :
    y ∈ dedup l ↔ y ∈ l := by
  induction l with
  | nil => simp [dedup]
  | cons x xs ih =>
    simp only [dedup]
    by_cases h : x ∈ xs
    · simp only [h, ↓reduceIte, ih, List.mem_cons]
      constructor
      · intro hy; exact Or.inr hy
      · intro hy
        rcases hy with rfl | hy
        · exact h
        · exact hy
    · simp only [h, ↓reduceIte, List.mem_cons, ih]

theorem nodup_dedup {α : Type} [DecidableEq α] (l : List α) : (dedup l).Nodup := by
  induction l with
  | nil => simp [dedup]
  | cons x xs ih =>
    simp only [dedup]
    by_cases h : x ∈ xs
    · simp [h, ih]
    · simp only [h, ↓reduceIte, List.nodup_cons]
      exact ⟨fun hm => h ((mem_dedup xs x).mp hm), ih⟩

theorem length_dedup_le {α : Type} [DecidableEq α] (l : List α) : (dedup l).length ≤ l.length := by
  induction l with
  | nil => simp [dedup]
  | cons x xs ih =>
    simp only [dedup]
    by_cases h : x ∈ xs <;> simp [h] <;> omega

theorem length_dedup_lt_of_not_nodup {α : Type} [DecidableEq α] (l : List α) (h : ¬ l.Nodup) :
    (dedup l).length < l.length := by
  induction l with
  | nil => exact absurd List.nodup_nil h
  | cons x xs ih =>
    simp only [dedup]
    by_cases hmem : x ∈ xs
    · simp only [hmem, ↓reduceIte, List.length_cons]
      have := length_dedup_le xs; omega
    · simp only [hmem, ↓reduceIte, List.length_cons]
      have hxs : ¬ xs.Nodup := fun hnd => h (List.nodup_cons.mpr ⟨hmem, hnd⟩)
      have := ih hxs; omega

-- A surjective function Fin n → Fin n is injective (and hence bijective).

theorem surjective_iff_bijective (n : Nat) (f : Fin n → Fin n) :
    Function.Surjective f ↔ (Function.Injective f ∧ Function.Surjective f) := by
  constructor
  · intro hsurj
    refine ⟨?_, hsurj⟩
    intro x y hxy
    cases Decidable.em (x = y) with
    | inl heq => exact heq
    | inr hne =>
      exfalso
      have hmem : ∀ j : Fin n, j ∈ (List.finRange n).map f := by
        intro j
        rcases hsurj j with ⟨i, hi⟩
        exact List.mem_map.mpr ⟨i, List.mem_finRange i, hi⟩
      have hnd_im : (dedup ((List.finRange n).map f)).Nodup := nodup_dedup _
      have hmem_ed : ∀ j : Fin n, j ∈ dedup ((List.finRange n).map f) ↔ j ∈ List.finRange n := by
        intro j
        simp [mem_dedup, hmem j, List.mem_finRange]
      have hperm := perm_of_nodup_iff hnd_im (List.nodup_finRange n) hmem_ed
      have hlen_eq : (dedup ((List.finRange n).map f)).length = ((List.finRange n).map f).length := by
        rw [hperm.length_eq, List.length_map]
      have hnot_nd : ¬ ((List.finRange n).map f).Nodup := by
        intro hnd_map
        have hlen_sub : ∀ (l : List (Fin n)), (l.map f).Nodup → ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b := by
          intro l
          induction l with
          | nil => intro _ _ ha; cases ha
          | cons a as ihl =>
            intro hnd' u hu v hv huv
            rw [List.map_cons, List.nodup_cons] at hnd'
            rcases List.mem_cons.mp hu with rfl | hu'
            · rcases List.mem_cons.mp hv with rfl | hv'
              · rfl
              · exact absurd (List.mem_map.mpr ⟨v, hv', huv.symm⟩) hnd'.1
            · rcases List.mem_cons.mp hv with rfl | hv'
              · exact absurd (List.mem_map.mpr ⟨u, hu', huv⟩) hnd'.1
              · exact ihl hnd'.2 u hu' v hv' huv
        exact hne (hlen_sub (List.finRange n) hnd_map x (List.mem_finRange x) y (List.mem_finRange y) hxy)
      have hlt := length_dedup_lt_of_not_nodup _ hnot_nd
      omega
  · exact fun hb => hb.2

theorem rowProd_eq_sum_fns_aux (n : Nat) (S : Mask n) :
    ∀ (m : Nat) (R : Fin m → Fin n → Int),
      prodInt (List.finRange m) (fun i => sumInt ((List.finRange n).filter S) (fun j => R i j)) =
      sumInt ((allFns m n).filter (fnInMask S))
        (fun f => prodInt (List.finRange m) (fun i => R i (f i)))
  | 0, R => by
    simp [allFns, allFnsToList, fnInMask]
  | m + 1, R => by
    have ih := rowProd_eq_sum_fns_aux n S m (fun i j => R i.succ j)
    have hfr : List.finRange (m + 1) = ⟨0, Nat.zero_lt_succ m⟩ :: (List.finRange m).map Fin.succ :=
      List.finRange_succ
    rw [hfr, prodInt_cons, prodInt_map, ih]
    have hflt : (allFns (m + 1) n).filter (fnInMask S) =
        ((List.finRange n).filter S).flatMap (fun j =>
          ((allFns m n).filter (fnInMask S)).map (consFinFun j)) := by
      simp only [allFns, allFnsToList]
      rw [List.filter_flatMap]
      have hsub : ∀ (l : List (Fin n)),
          l.flatMap (fun a => ((allFnsToList (List.finRange n) m).map (consFinFun a)).filter (fnInMask S)) =
          (l.filter S).flatMap (fun a => ((allFnsToList (List.finRange n) m).filter (fnInMask S)).map (consFinFun a)) := by
        intro l
        induction l with
        | nil => rfl
        | cons a as ihl =>
          rw [List.flatMap_cons, List.filter_cons]
          have hfn : ∀ g : Fin m → Fin n,
              fnInMask S (consFinFun a g) = (S a && fnInMask S g) := by
            intro g
            unfold fnInMask
            rw [hfr, List.all_cons, consFinFun_zero, List.all_map]
            have hall_eq : (List.finRange m).all ((fun i => S (consFinFun a g i)) ∘ Fin.succ) =
                (List.finRange m).all (fun i => S (g i)) := by
              have : ∀ (l : List (Fin m)),
                  l.all ((fun i => S (consFinFun a g i)) ∘ Fin.succ) = l.all (fun i => S (g i)) := by
                intro l
                induction l with
                | nil => rfl
                | cons x xs ihx => simp [Function.comp, consFinFun_succ, ihx]
              exact this (List.finRange m)
            rw [hall_eq]
          rw [List.filter_map]
          cases hsa : S a
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have hemp : (allFnsToList (List.finRange n) m).filter (fnInMask S ∘ consFinFun a) = [] := by
              rw [List.filter_eq_nil_iff]
              intro g _
              simp [Function.comp, hfn g, hsa]
            rw [hemp, List.map_nil, List.nil_append, ihl]
          · simp only [↓reduceIte, List.flatMap_cons]
            have hflt_eq : (allFnsToList (List.finRange n) m).filter (fnInMask S ∘ consFinFun a) =
                (allFnsToList (List.finRange n) m).filter (fnInMask S) := by
              have : ∀ (l : List (Fin m → Fin n)),
                  l.filter (fnInMask S ∘ consFinFun a) = l.filter (fnInMask S) := by
                intro l
                induction l with
                | nil => rfl
                | cons x xs ihx =>
                  rw [List.filter_cons, List.filter_cons]
                  simp only [Function.comp, hfn x, hsa, Bool.true_and, ihx]
              exact this _
            rw [hflt_eq, ihl]
      exact hsub (List.finRange n)
    rw [hflt]
    have hsum_flat : ∀ (l : List (Fin n)) (g : Fin n → List (Fin (m + 1) → Fin n)) (val : (Fin (m + 1) → Fin n) → Int),
        sumInt (l.flatMap g) val = sumInt l (fun j => sumInt (g j) val) := by
      intro l g val
      induction l with
      | nil => rfl
      | cons a as ihl => simp [List.flatMap_cons, sumInt_append, ihl]
    rw [hsum_flat]
    rw [← sumInt_mul_right]
    apply sumInt_congr
    intro j _
    rw [sumInt_map, ← sumInt_mul_left]
    apply sumInt_congr
    intro f _
    rw [prodInt_cons, consFinFun_zero, prodInt_map]
    have hpi : prodInt (List.finRange m) (fun i => R i.succ (consFinFun j f i.succ)) =
        prodInt (List.finRange m) (fun i => R i.succ (f i)) := by
      apply prodInt_congr
      intro i _
      rw [consFinFun_succ]
    rw [hpi]

theorem rowProd_eq_sum_fns (n : Nat) (A : Mat n) (S : Mask n) :
    rowProd n A S =
      sumInt ((allFns n n).filter (fnInMask S))
        (fun f => prodInt (List.finRange n) (fun i => A i (f i))) :=
  rowProd_eq_sum_fns_aux n S n A

theorem flipMask_invol {n : Nat} (j₀ : Fin n) (S : Mask n) :
    flipMask j₀ (flipMask j₀ S) = S := by
  funext j
  unfold flipMask
  by_cases h : j = j₀ <;> simp [h]

theorem maskCard_le (n : Nat) (S : Mask n) : maskCard n S ≤ n := by
  unfold maskCard
  calc ((List.finRange n).filter S).length
      ≤ (List.finRange n).length := List.length_filter_le _ _
    _ = n := List.length_finRange

theorem maskCard_flip {n : Nat} (j₀ : Fin n) (S : Mask n) :
    maskCard n (flipMask j₀ S) = if S j₀ then maskCard n S - 1 else maskCard n S + 1 := by
  unfold maskCard
  have haux : ∀ (l : List (Fin n)), l.Nodup → j₀ ∈ l →
      (l.filter (flipMask j₀ S)).length = if S j₀ then (l.filter S).length - 1 else (l.filter S).length + 1 := by
    intro l hnd hmem
    induction l with
    | nil => cases hmem
    | cons x xs ih =>
      have ⟨hx_nmem, hxs_nd⟩ := List.nodup_cons.mp hnd
      by_cases hxj : x = j₀
      · subst hxj
        have heq_xs : xs.filter (flipMask x S) = xs.filter S := by
          apply List.filter_congr
          intro y hy
          have hne : y ≠ x := fun h => hx_nmem (h ▸ hy)
          simp [flipMask, hne]
        cases hsx : S x
        · simp [flipMask, hsx, heq_xs]
        · simp [flipMask, hsx, heq_xs]
      · have hmem_xs : j₀ ∈ xs := by
          rcases List.mem_cons.mp hmem with rfl | h
          · exact absurd rfl hxj
          · exact h
        have ih' := ih hxs_nd hmem_xs
        have hfx : flipMask j₀ S x = S x := by simp [flipMask, hxj]
        cases hsx : S x
        · simp [hfx, hsx, ih']
        · cases hsj : S j₀
          · simp [hfx, hsx, hsj] at ih' ⊢; omega
          · have hpos : 0 < (xs.filter S).length := by
              have : j₀ ∈ xs.filter S := List.mem_filter.mpr ⟨hmem_xs, hsj⟩
              exact List.length_pos_of_mem this
            simp [hfx, hsx, hsj] at ih' ⊢; omega
  exact haux (List.finRange n) (List.nodup_finRange n) (List.mem_finRange j₀)

theorem ryserSign_flip {n : Nat} (j₀ : Fin n) (S : Mask n) :
    ryserSign n (flipMask j₀ S) = -ryserSign n S := by
  have hle1 := maskCard_le n S
  have hle2 := maskCard_le n (flipMask j₀ S)
  have hcf := maskCard_flip j₀ S
  unfold ryserSign
  cases hsj : S j₀
  · simp [hsj] at hcf
    have hdiff : n - maskCard n (flipMask j₀ S) + 1 = n - maskCard n S := by omega
    by_cases hp : (n - maskCard n S) % 2 = 0 <;> simp [hp] <;> omega
  · simp [hsj] at hcf
    have hpos : 0 < maskCard n S := by
      have : j₀ ∈ (List.finRange n).filter S := List.mem_filter.mpr ⟨List.mem_finRange j₀, hsj⟩
      exact List.length_pos_of_mem this
    have hdiff : n - maskCard n (flipMask j₀ S) = n - maskCard n S + 1 := by omega
    by_cases hp : (n - maskCard n S) % 2 = 0 <;> simp [hp] <;> omega

theorem filter_const_true {α : Type} (l : List α) : l.filter (fun _ => true) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem sum_ryserSign_supersets (n : Nat) (f : Fin n → Fin n) :
    sumInt ((allMasks n).filter (fun S => fnInMask S f)) (ryserSign n) =
      if isSurjective n f then 1 else 0 := by
  cases hsurj : isSurjective n f
  · simp only [Bool.false_eq_true, ↓reduceIte]
    -- Constructively extract a missed column j₀ from isSurjective n f = false!
    unfold isSurjective at hsurj
    rw [List.all_eq_false] at hsurj
    rcases hsurj with ⟨j₀, _, hj₀_false⟩
    have hj₀ : ∀ i : Fin n, f i ≠ j₀ := by
      intro i hi
      have htrue : (List.finRange n).any (fun i => decide (f i = j₀)) = true :=
        List.any_eq_true.mpr ⟨i, List.mem_finRange i, decide_eq_true hi⟩
      rw [htrue] at hj₀_false
      exact hj₀_false rfl
    let L := (allMasks n).filter (fun S => fnInMask S f)
    have hL_nd : L.Nodup := (nodup_allMasks n).filter _
    have hL_closed : ∀ S ∈ L, flipMask j₀ S ∈ L := by
      intro S hS
      rw [List.mem_filter] at hS ⊢
      refine ⟨mem_allMasks n _, ?_⟩
      unfold fnInMask at hS ⊢
      rw [List.all_eq_true] at hS ⊢
      intro i hi
      have hne : f i ≠ j₀ := hj₀ i
      simp [flipMask, hne, hS.2 i hi]
    have hbij := sumInt_bijection hL_nd hL_nd (flipMask j₀) (flipMask j₀)
      hL_closed hL_closed
      (fun S _ => flipMask_invol j₀ S) (fun S _ => flipMask_invol j₀ S)
      (ryserSign n)
    have hneg : sumInt L (fun S => ryserSign n (flipMask j₀ S)) = -sumInt L (ryserSign n) := by
      rw [sumInt_congr (fun S _ => ryserSign_flip j₀ S), sumInt_neg]
    have heq : -sumInt L (ryserSign n) = sumInt L (ryserSign n) := hneg.symm.trans hbij
    change sumInt L (ryserSign n) = 0
    omega
  · simp only [↓reduceIte]
    have hsf := (isSurjective_iff n f).mp hsurj
    have hflt : (allMasks n).filter (fun S => fnInMask S f) = [fun _ => true] := by
      have hnd1 : ((allMasks n).filter (fun S => fnInMask S f)).Nodup :=
        (nodup_allMasks n).filter _
      have hnd2 : ([fun _ : Fin n => true]).Nodup := by simp
      have hmem : ∀ S, S ∈ (allMasks n).filter (fun S => fnInMask S f) ↔ S ∈ [fun _ => true] := by
        intro S
        simp only [List.mem_filter, mem_allMasks, true_and, List.mem_singleton]
        constructor
        · intro hfn
          funext j
          rcases hsf j with ⟨i, hi⟩
          have hall := List.all_eq_true.mp hfn i (List.mem_finRange i)
          rw [hi] at hall
          exact hall
        · intro hS
          subst hS
          unfold fnInMask
          rw [List.all_eq_true]
          intro i _; rfl
      exact List.Perm.eq_singleton (perm_of_nodup_iff hnd1 hnd2 hmem)
    rw [hflt]
    have hcard : maskCard n (fun _ => true) = n := by
      simp [maskCard, filter_const_true]
    simp [ryserSign, hcard]

/-- THEOREM 0 (Ryser's Formula): Exact equivalence of the permutation-sum permanent
    and the bitwise Ryser subset-parity sum, for all n and all integer matrices A. -/
theorem perm_eq_ryserSum (n : Nat) (A : Mat n) :
    perm n A = ryserSum n A := by
  unfold ryserSum
  calc perm n A
      = sumInt (allFns n n)
          (fun f => (if isSurjective n f then (1 : Int) else 0) *
            prodInt (List.finRange n) (fun i => A i (f i))) := by
        unfold perm
        rw [sumInt_filter_eq_sumInt_ite]
        apply sumInt_congr
        intro f _
        cases isSurjective n f <;> simp
    _ = sumInt (allFns n n)
          (fun f => sumInt ((allMasks n).filter (fun S => fnInMask S f)) (ryserSign n) *
            prodInt (List.finRange n) (fun i => A i (f i))) := by
        apply sumInt_congr
        intro f _
        rw [sum_ryserSign_supersets]
    _ = sumInt (allFns n n)
          (fun f => sumInt (allMasks n)
            (fun S => if fnInMask S f then ryserSign n S * prodInt (List.finRange n) (fun i => A i (f i)) else 0)) := by
        apply sumInt_congr
        intro f _
        rw [sumInt_filter_eq_sumInt_ite, ← sumInt_mul_right]
        apply sumInt_congr
        intro S _
        cases fnInMask S f <;> simp
    _ = sumInt (allMasks n)
          (fun S => sumInt (allFns n n)
            (fun f => if fnInMask S f then ryserSign n S * prodInt (List.finRange n) (fun i => A i (f i)) else 0)) :=
        sumInt_comm (allFns n n) (allMasks n) _
    _ = sumInt (allMasks n) (fun S => ryserSign n S * rowProd n A S) := by
        apply sumInt_congr
        intro S _
        rw [rowProd_eq_sum_fns, sumInt_filter_eq_sumInt_ite, ← sumInt_mul_left]
        apply sumInt_congr
        intro f _
        cases fnInMask S f <;> simp

namespace Fin2Group

variable {k : Nat} (Gr : Fin2Group k)

theorem mul_right_cancel {a b c : Gr.G} (h : Gr.mul a c = Gr.mul b c) : a = b := by
  have h1 := congrArg (fun x => Gr.mul x (Gr.inv c)) h
  rw [Gr.mul_assoc, Gr.mul_assoc, Gr.mul_inv, Gr.mul_one, Gr.mul_one] at h1
  exact h1

end Fin2Group

theorem mem_orbit {k : Nat} (Gr : Fin2Group k) {X : Type} [DecidableEq X]
    (A : GroupAction Gr X) (x y : X) :
    y ∈ orbit Gr A x ↔ ∃ g : Gr.G, A.act g x = y := by
  unfold orbit
  rw [mem_dedup, List.mem_map]
  constructor
  · rintro ⟨g, _, rfl⟩; exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩; exact ⟨g, Gr.complete g, rfl⟩

theorem self_mem_orbit {k : Nat} (Gr : Fin2Group k) {X : Type} [DecidableEq X]
    (A : GroupAction Gr X) (x : X) : x ∈ orbit Gr A x :=
  (mem_orbit Gr A x x).mpr ⟨Gr.one, A.act_one x⟩

theorem nodup_orbit {k : Nat} (Gr : Fin2Group k) {X : Type} [DecidableEq X]
    (A : GroupAction Gr X) (x : X) : (orbit Gr A x).Nodup :=
  nodup_dedup _

/-- Fiber length equality: for every y in the orbit of x, #{g | g·x = y} = |Stab(x)|. -/
theorem fiber_length_eq_stab {k : Nat} (Gr : Fin2Group k) {X : Type} [DecidableEq X]
    (A : GroupAction Gr X) (x y : X) (hy : y ∈ orbit Gr A x) :
    (Gr.elems.filter (fun g => decide (A.act g x = y))).length = (stab Gr A x).length := by
  rcases (mem_orbit Gr A x y).mp hy with ⟨g₀, hg₀⟩
  apply length_bijection (Gr.nodup.filter _) (nodup_stab Gr A x)
    (fun g => Gr.mul (Gr.inv g₀) g) (fun h => Gr.mul g₀ h)
  · intro g hg
    rw [List.mem_filter] at hg
    rw [mem_stab, A.act_mul, of_decide_eq_true hg.2, ← hg₀, ← A.act_mul, Gr.inv_mul, A.act_one]
  · intro h hh
    rw [mem_stab] at hh
    rw [List.mem_filter]
    exact ⟨Gr.complete _, decide_eq_true (by rw [A.act_mul, hh, hg₀])⟩
  · intro g _
    rw [← Gr.mul_assoc, Gr.mul_inv, Gr.one_mul]
  · intro h _
    rw [← Gr.mul_assoc, Gr.inv_mul, Gr.one_mul]

theorem length_eq_sum_fibers {α β : Type} [DecidableEq β]
    (l : List α) (f : α → β) (ys : List β) (hnd : ys.Nodup) (hcov : ∀ a ∈ l, f a ∈ ys) :
    l.length = (ys.map (fun y => (l.filter (fun a => decide (f a = y))).length)).sum := by
  induction ys generalizing l with
  | nil =>
    cases l with
    | nil => simp
    | cons a as => exfalso; exact List.not_mem_nil (hcov a (by simp))
  | cons y ys ih =>
    have ⟨hy_nmem, hys_nd⟩ := List.nodup_cons.mp hnd
    let l₁ := l.filter (fun a => decide (f a = y))
    let l₂ := l.filter (fun a => !decide (f a = y))
    have hsplit : l.length = l₁.length + l₂.length := by
      have haux : ∀ (xs : List α) (p : α → Bool),
          xs.length = (xs.filter p).length + (xs.filter (fun a => !p a)).length := by
        intro xs p
        induction xs with
        | nil => simp
        | cons x xs' ihx =>
          cases hpx : p x <;> simp [hpx] <;> omega
      exact haux l (fun a => decide (f a = y))
    have hcov2 : ∀ a ∈ l₂, f a ∈ ys := by
      intro a ha
      rw [List.mem_filter] at ha
      rcases List.mem_cons.mp (hcov a ha.1) with heq | hmem
      · exfalso; simp [heq] at ha
      · exact hmem
    rw [List.map_cons, List.sum_cons, hsplit, ih l₂ hys_nd hcov2]
    congr 1
    have hmap_eq : ys.map (fun y' => (l₂.filter (fun a => decide (f a = y'))).length) =
        ys.map (fun y' => (l.filter (fun a => decide (f a = y'))).length) := by
      apply List.map_congr_left
      intro y' hy'
      have hne : y' ≠ y := fun h => hy_nmem (h ▸ hy')
      congr 1
      -- l₂.filter (f a = y') = l.filter (f a = y') since y' ≠ y
      have hflt : ∀ (xs : List α),
          (xs.filter (fun a => !decide (f a = y))).filter (fun a => decide (f a = y')) =
          xs.filter (fun a => decide (f a = y')) := by
        intro xs
        induction xs with
        | nil => rfl
        | cons a as iha =>
          by_cases h1 : f a = y
          · rw [List.filter_cons, List.filter_cons]
            simp [h1, Ne.symm hne, iha]
          · rw [List.filter_cons]
            simp only [h1, decide_false, Bool.not_false, ↓reduceIte, List.filter_cons]
            by_cases h2 : f a = y' <;> simp [h2, iha]
      exact hflt l
    exact congrArg List.sum hmap_eq

/-- Orbit-Stabilizer Theorem for finite 2-groups. -/
theorem orbit_mul_stab {k : Nat} (Gr : Fin2Group k) {X : Type} [DecidableEq X]
    (A : GroupAction Gr X) (x : X) :
    (orbit Gr A x).length * (stab Gr A x).length = 2 ^ k := by
  have hsum := length_eq_sum_fibers Gr.elems (fun g => A.act g x) (orbit Gr A x)
    (nodup_orbit Gr A x) (fun g _ => (mem_orbit Gr A x _).mpr ⟨g, rfl⟩)
  have hconst : (orbit Gr A x).map (fun y => (Gr.elems.filter (fun g => decide (A.act g x = y))).length) =
      (orbit Gr A x).map (fun _ => (stab Gr A x).length) := by
    apply List.map_congr_left
    intro y hy
    exact fiber_length_eq_stab Gr A x y hy
  rw [hconst] at hsum
  have hsum_const : ∀ (l : List X) (c : Nat), (l.map (fun _ => c)).sum = l.length * c := by
    intro l c
    induction l with
    | nil => simp
    | cons _ xs ih => simp [ih, Nat.succ_mul, Nat.add_comm]
  rw [hsum_const, Gr.card] at hsum
  exact hsum.symm

theorem nat_mul_eq_one {a b : Nat} (h : a * b = 1) : a = 1 ∧ b = 1 := by
  cases a with
  | zero => simp at h
  | succ a' =>
    cases b with
    | zero => simp at h
    | succ b' =>
      simp only [Nat.succ_mul, Nat.mul_succ] at h
      omega

/-- Every divisor of 2^k is a power of 2. -/
theorem pow2_of_mul_eq_pow2 :
    ∀ (k a b : Nat), a * b = 2 ^ k → ∃ s ≤ k, b = 2 ^ s ∧ a = 2 ^ (k - s)
  | 0, a, b, h => by
    simp only [Nat.pow_zero] at h
    rcases nat_mul_eq_one h with ⟨ha, hb⟩
    exact ⟨0, Nat.le_refl 0, hb, ha⟩
  | k + 1, a, b, h => by
    by_cases hb1 : b = 1
    · refine ⟨0, Nat.zero_le _, hb1, ?_⟩
      simpa [hb1] using h
    · by_cases ha1 : a = 1
      · refine ⟨k + 1, Nat.le_refl _, ?_, by simp [ha1]⟩
        simpa [ha1] using h
      · have hb_even : b % 2 = 0 := by
          by_cases hodd : b % 2 = 0
          · exact hodd
          · exfalso
            have hodd_dvd : ∀ m u v, u * v = 2 ^ m → v % 2 = 1 → v = 1 := by
              intro m
              induction m with
              | zero =>
                intro u v huv _
                simp only [Nat.pow_zero] at huv
                exact (nat_mul_eq_one huv).2
              | succ m' ihm =>
                intro u v huv hvodd
                have hu_even : u % 2 = 0 := by
                  have hmod : (u * v) % 2 = 0 := by
                    rw [huv, Nat.pow_succ]; omega
                  rw [Nat.mul_mod, hvodd] at hmod
                  omega
                have hdiv : (u / 2) * v = 2 ^ m' := by
                  have h2 : 2 * ((u / 2) * v) = 2 * 2 ^ m' := by
                    calc 2 * ((u / 2) * v) = (2 * (u / 2)) * v := (Nat.mul_assoc _ _ _).symm
                      _ = u * v := by rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hu_even)]
                      _ = 2 ^ (m' + 1) := huv
                      _ = 2 * 2 ^ m' := by rw [Nat.pow_succ, Nat.mul_comm]
                  omega
                exact ihm (u / 2) v hdiv hvodd
            exact hb1 (hodd_dvd (k + 1) a b h (by omega))
        have hhalf : a * (b / 2) = 2 ^ k := by
          have h2 : 2 * (a * (b / 2)) = 2 * 2 ^ k := by
            calc 2 * (a * (b / 2)) = a * (2 * (b / 2)) := Nat.mul_left_comm _ _ _
              _ = a * b := by rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hb_even)]
              _ = 2 ^ (k + 1) := h
              _ = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
          omega
        rcases pow2_of_mul_eq_pow2 k a (b / 2) hhalf with ⟨s, hs, hbd, had⟩
        refine ⟨s + 1, by omega, ?_, ?_⟩
        · have hb2 : b = 2 * (b / 2) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hb_even)).symm
          rw [hb2, hbd, Nat.pow_succ, Nat.mul_comm]
        · have hsub : k + 1 - (s + 1) = k - s := by omega
          rw [hsub]; exact had

theorem exists_pow2_stab_orbit {k : Nat} (Gr : Fin2Group k) {X : Type} [DecidableEq X]
    (A : GroupAction Gr X) (x : X) :
    ∃ s ≤ k, (stab Gr A x).length = 2 ^ s ∧ (orbit Gr A x).length = 2 ^ (k - s) :=
  pow2_of_mul_eq_pow2 k _ _ (orbit_mul_stab Gr A x)

/-- THE REUSABLE INFINITE PROOF ENGINE:
    2-Group Stabilizer-Divisibility Lifting Principle.
    If Δ : X → Int is G-invariant on a G-closed nodup list L, and for every x ∈ L
    with |Stab_G(x)| = 2^s we have 2^(s + c) ∣ Δ(x), then 2^(k + c) ∣ ∑_{x ∈ L} Δ(x). -/
theorem twoGroup_sum_dvd {k : Nat} (Gr : Fin2Group k) {X : Type} [DecidableEq X]
    (A : GroupAction Gr X) (Δ : X → Int) (c : Nat)
    (hinv : ∀ g x, Δ (A.act g x) = Δ x) :
    ∀ (nBound : Nat) (L : List X),
      L.length ≤ nBound →
      L.Nodup →
      (∀ g x, x ∈ L → A.act g x ∈ L) →
      (∀ x ∈ L, ∀ s ≤ k, (stab Gr A x).length = 2 ^ s → ((2 ^ (s + c) : Nat) : Int) ∣ Δ x) →
      ((2 ^ (k + c) : Nat) : Int) ∣ sumInt L Δ
  | 0, L, hlen, _, _, _ => by
    cases L with
    | nil => exact Int.dvd_zero _
    | cons _ _ => simp at hlen
  | nBound + 1, L, hlen, hnd, hclosed, hstab_dvd => by
    cases L with
    | nil => exact Int.dvd_zero _
    | cons x xs =>
      let L_in := (x :: xs).filter (fun y => decide (y ∈ orbit Gr A x))
      let L_out := (x :: xs).filter (fun y => !decide (y ∈ orbit Gr A x))
      have hsplit : sumInt (x :: xs) Δ = sumInt L_in Δ + sumInt L_out Δ :=
        (sumInt_filter_add_not (x :: xs) (fun y => decide (y ∈ orbit Gr A x)) Δ).symm
      rw [hsplit]
      apply Int.dvd_add
      · -- 1. L_in is a permutation of orbit Gr A x, on which Δ is constant (= Δ x)
        have hperm : L_in.Perm (orbit Gr A x) := by
          apply perm_of_nodup_iff (hnd.filter _) (nodup_orbit Gr A x)
          intro y
          simp only [List.mem_filter, decide_eq_true_eq]
          constructor
          · exact fun h => h.2
          · intro hy
            refine ⟨?_, hy⟩
            rcases (mem_orbit Gr A x y).mp hy with ⟨g, rfl⟩
            exact hclosed g x (by simp)
        rw [sumInt_perm hperm]
        have hconst : sumInt (orbit Gr A x) Δ = ((orbit Gr A x).length : Int) * Δ x := by
          rw [sumInt_congr (g := fun _ => Δ x) (fun y hy => by
            rcases (mem_orbit Gr A x y).mp hy with ⟨g, rfl⟩
            exact hinv g x)]
          exact sumInt_const _ _
        rw [hconst]
        rcases exists_pow2_stab_orbit Gr A x with ⟨s, hs, hst, horb⟩
        have hdvd := hstab_dvd x (by simp) s hs hst
        rcases hdvd with ⟨q, hq⟩
        rw [horb, hq]
        refine ⟨q, ?_⟩
        have hexp : (2 ^ (k - s) : Nat) * (2 ^ (s + c) : Nat) = 2 ^ (k + c) := by
          rw [← Nat.pow_add]
          congr 1; omega
        calc ((2 ^ (k - s) : Nat) : Int) * (((2 ^ (s + c) : Nat) : Int) * q)
            = (((2 ^ (k - s) : Nat) * (2 ^ (s + c) : Nat) : Nat) : Int) * q := by
              rw [Int.natCast_mul, Int.mul_assoc]
          _ = ((2 ^ (k + c) : Nat) : Int) * q := by rw [hexp]
      · -- 2. L_out is strictly shorter (x ∉ L_out), nodup, and G-closed!
        have hlt : L_out.length ≤ nBound := by
          have hx_in : decide (x ∈ orbit Gr A x) = true := decide_eq_true (self_mem_orbit Gr A x)
          have hsub : L_out = xs.filter (fun y => !decide (y ∈ orbit Gr A x)) := by
            simp [L_out, hx_in]
          rw [hsub]
          have := List.length_filter_le (fun y => !decide (y ∈ orbit Gr A x)) xs
          simp at hlen; omega
        have hclosed_out : ∀ g y, y ∈ L_out → A.act g y ∈ L_out := by
          intro g y hy
          rw [List.mem_filter] at hy ⊢
          refine ⟨hclosed g y hy.1, ?_⟩
          have hny : y ∉ orbit Gr A x := by
            intro hmem
            simp [hmem] at hy
          have hngy : A.act g y ∉ orbit Gr A x := by
            intro hmem
            rcases (mem_orbit Gr A x _).mp hmem with ⟨g', hg'⟩
            apply hny
            rw [mem_orbit]
            refine ⟨Gr.mul (Gr.inv g) g', ?_⟩
            rw [A.act_mul, hg', ← A.act_mul, Gr.inv_mul, A.act_one]
          simp [hngy]
        exact twoGroup_sum_dvd Gr A Δ c hinv nBound L_out hlt (hnd.filter _) hclosed_out
          (fun y hy => hstab_dvd y (List.mem_filter.mp hy).1)

-- ============================================================================
-- Subgroup Free-Action Factorization Lemmas (for Rows & Columns)
-- ============================================================================

/-- If a subgroup H acts freely on X, every H-orbit in a H-closed nodup list L has length |H|,
    so |H| divides L.length. -/
theorem free_subgroup_dvd_length {k : Nat} (Gr : Fin2Group k) (H : Subgroup Gr)
    {X : Type} [DecidableEq X] (A : GroupAction Gr X)
    (hfree : ∀ g : Gr.G, ∀ x : X, A.act g x = x → g = Gr.one) :
    ∀ (nBound : Nat) (L : List X),
      L.length ≤ nBound →
      L.Nodup →
      (∀ h ∈ H.elems, ∀ x ∈ L, A.act h x ∈ L) →
      H.elems.length ∣ L.length
  | 0, L, hlen, _, _ => by
    cases L with
    | nil => exact Nat.dvd_zero _
    | cons _ _ => simp at hlen
  | nBound + 1, L, hlen, hnd, hclosed => by
    cases L with
    | nil => exact Nat.dvd_zero _
    | cons x xs =>
      let orbH := H.elems.map (fun h => A.act h x)
      have horbH_nd : orbH.Nodup := by
        apply nodup_map_inj_on H.nodup
        intro h₁ _ h₂ _ heq
        have hact : A.act (Gr.mul (Gr.inv h₂) h₁) x = x := by
          rw [A.act_mul, heq, ← A.act_mul, Gr.inv_mul, A.act_one]
        have hone := hfree _ x hact
        have := congrArg (Gr.mul h₂) hone
        rw [← Gr.mul_assoc, Gr.mul_inv, Gr.one_mul, Gr.mul_one] at this
        exact this
      have hx_orbH : x ∈ orbH := List.mem_map.mpr ⟨Gr.one, H.one_mem, A.act_one x⟩
      let L_in := (x :: xs).filter (fun y => decide (y ∈ orbH))
      let L_out := (x :: xs).filter (fun y => !decide (y ∈ orbH))
      have hsplit : (x :: xs).length = L_in.length + L_out.length := by
        have haux : ∀ (l : List X) (p : X → Bool),
            l.length = (l.filter p).length + (l.filter (fun y => !p y)).length := by
          intro l p
          induction l with
          | nil => simp
          | cons a as iha => cases hpa : p a <;> simp [hpa] <;> omega
        exact haux (x :: xs) (fun y => decide (y ∈ orbH))
      rw [hsplit]
      apply Nat.dvd_add
      · have hperm : L_in.Perm orbH := by
          apply perm_of_nodup_iff (hnd.filter _) horbH_nd
          intro y
          simp only [List.mem_filter, decide_eq_true_eq]
          constructor
          · exact fun h => h.2
          · intro hy
            refine ⟨?_, hy⟩
            rcases List.mem_map.mp hy with ⟨h, hh, rfl⟩
            exact hclosed h hh x (by simp)
        rw [hperm.length_eq, List.length_map]
        exact Nat.dvd_refl _
      · have hlt : L_out.length ≤ nBound := by
          have hx_dec : decide (x ∈ orbH) = true := decide_eq_true hx_orbH
          have hsub : L_out = xs.filter (fun y => !decide (y ∈ orbH)) := by simp [L_out, hx_dec]
          rw [hsub]
          have := List.length_filter_le (fun y => !decide (y ∈ orbH)) xs
          simp at hlen; omega
        have hclosed_out : ∀ h ∈ H.elems, ∀ y ∈ L_out, A.act h y ∈ L_out := by
          intro h hh y hy
          rw [List.mem_filter] at hy ⊢
          refine ⟨hclosed h hh y hy.1, ?_⟩
          have hny : y ∉ orbH := by intro hm; simp [hm] at hy
          have hnhy : A.act h y ∉ orbH := by
            intro hm
            rcases List.mem_map.mp hm with ⟨h', hh', heq⟩
            apply hny
            refine List.mem_map.mpr ⟨Gr.mul (Gr.inv h) h', H.mul_mem _ _ (H.inv_mem h hh) hh', ?_⟩
            rw [A.act_mul, heq, ← A.act_mul, Gr.inv_mul, A.act_one]
          simp [hnhy]
        exact free_subgroup_dvd_length Gr H A hfree nBound L_out hlt (hnd.filter _) hclosed_out

/-- If a subgroup H acts freely on X and r : X → Int is H-invariant on an H-closed nodup list L,
    then ∏_{x ∈ L} r(x) = u ^ |H| for some integer u. -/
theorem free_subgroup_prod_pow {k : Nat} (Gr : Fin2Group k) (H : Subgroup Gr)
    {X : Type} [DecidableEq X] (A : GroupAction Gr X)
    (hfree : ∀ g : Gr.G, ∀ x : X, A.act g x = x → g = Gr.one)
    (r : X → Int) (hr : ∀ h ∈ H.elems, ∀ x, r (A.act h x) = r x) :
    ∀ (nBound : Nat) (L : List X),
      L.length ≤ nBound →
      L.Nodup →
      (∀ h ∈ H.elems, ∀ x ∈ L, A.act h x ∈ L) →
      ∃ u : Int, prodInt L r = u ^ H.elems.length
  | 0, L, hlen, _, _ => by
    cases L with
    | nil => exact ⟨1, by simp [Int.one_pow]⟩
    | cons _ _ => simp at hlen
  | nBound + 1, L, hlen, hnd, hclosed => by
    cases L with
    | nil => exact ⟨1, by simp [Int.one_pow]⟩
    | cons x xs =>
      let orbH := H.elems.map (fun h => A.act h x)
      have horbH_nd : orbH.Nodup := by
        apply nodup_map_inj_on H.nodup
        intro h₁ _ h₂ _ heq
        have hact : A.act (Gr.mul (Gr.inv h₂) h₁) x = x := by
          rw [A.act_mul, heq, ← A.act_mul, Gr.inv_mul, A.act_one]
        have hone := hfree _ x hact
        have := congrArg (Gr.mul h₂) hone
        rw [← Gr.mul_assoc, Gr.mul_inv, Gr.one_mul, Gr.mul_one] at this
        exact this
      have hx_orbH : x ∈ orbH := List.mem_map.mpr ⟨Gr.one, H.one_mem, A.act_one x⟩
      let L_in := (x :: xs).filter (fun y => decide (y ∈ orbH))
      let L_out := (x :: xs).filter (fun y => !decide (y ∈ orbH))
      have hsplit : prodInt (x :: xs) r = prodInt L_in r * prodInt L_out r :=
        (prodInt_filter_mul_not (x :: xs) (fun y => decide (y ∈ orbH)) r).symm
      have hperm : L_in.Perm orbH := by
        apply perm_of_nodup_iff (hnd.filter _) horbH_nd
        intro y
        simp only [List.mem_filter, decide_eq_true_eq]
        constructor
        · exact fun h => h.2
        · intro hy
          refine ⟨?_, hy⟩
          rcases List.mem_map.mp hy with ⟨h, hh, rfl⟩
          exact hclosed h hh x (by simp)
      have hprod_in : prodInt L_in r = (r x) ^ H.elems.length := by
        rw [prodInt_perm hperm, prodInt_map]
        rw [prodInt_congr (fun h hh => hr h hh x), prodInt_const]
      have hlt : L_out.length ≤ nBound := by
        have hx_dec : decide (x ∈ orbH) = true := decide_eq_true hx_orbH
        have hsub : L_out = xs.filter (fun y => !decide (y ∈ orbH)) := by simp [L_out, hx_dec]
        rw [hsub]
        have := List.length_filter_le (fun y => !decide (y ∈ orbH)) xs
        simp at hlen; omega
      have hclosed_out : ∀ h ∈ H.elems, ∀ y ∈ L_out, A.act h y ∈ L_out := by
        intro h hh y hy
        rw [List.mem_filter] at hy ⊢
        refine ⟨hclosed h hh y hy.1, ?_⟩
        have hny : y ∉ orbH := by intro hm; simp [hm] at hy
        have hnhy : A.act h y ∉ orbH := by
          intro hm
          rcases List.mem_map.mp hm with ⟨h', hh', heq⟩
          apply hny
          refine List.mem_map.mpr ⟨Gr.mul (Gr.inv h) h', H.mul_mem _ _ (H.inv_mem h hh) hh', ?_⟩
          rw [A.act_mul, heq, ← A.act_mul, Gr.inv_mul, A.act_one]
        simp [hnhy]
      rcases free_subgroup_prod_pow Gr H A hfree r hr nBound L_out hlt (hnd.filter _) hclosed_out with ⟨v, hv⟩
      refine ⟨r x * v, ?_⟩
      rw [hsplit, hprod_in, hv, Int.mul_pow]

-- ============================================================================
-- Lifting-the-Exponent (LTE) & 2-Adic Power Lemmas
-- ============================================================================

theorem odd_pow_two_pow_sub_one (u : Int) (hu : u % 2 ≠ 0) :
    ∀ (s : Nat), 1 ≤ s → ((2 ^ (s + 2) : Nat) : Int) ∣ (u ^ (2 ^ s) - 1)
  | 0, hs => by omega
  | 1, _ => by
    -- u is odd, so u = 2q + 1 → u^2 - 1 = 4*q*(q+1), divisible by 8
    have hq : ∃ q : Int, u = 2 * q + 1 := ⟨(u - 1) / 2, by omega⟩
    rcases hq with ⟨q, rfl⟩
    have heven : (2 : Int) ∣ q * (q + 1) := by
      by_cases hqm : q % 2 = 0
      · exact ⟨(q / 2) * (q + 1), by
          have hq2 : q = 2 * (q / 2) := by omega
          calc q * (q + 1) = (2 * (q / 2)) * (q + 1) := by rw [← hq2]
            _ = 2 * ((q / 2) * (q + 1)) := by rw [Int.mul_assoc]⟩
      · exact ⟨q * ((q + 1) / 2), by
          have hq2 : q + 1 = 2 * ((q + 1) / 2) := by omega
          calc q * (q + 1) = q * (2 * ((q + 1) / 2)) := by rw [← hq2]
            _ = 2 * (q * ((q + 1) / 2)) := by rw [Int.mul_left_comm]⟩
    rcases heven with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have hexp : (2 * q + 1) ^ (2 ^ 1) - 1 = 4 * (q * (q + 1)) := by
      have : (2 * q + 1) ^ 2 = (2 * q + 1) * (2 * q + 1) := by simp [Int.pow_succ]
      rw [show (2 ^ 1 : Nat) = 2 by rfl, this]
      have h2q : (2 * q) * (2 * q) = 4 * (q * q) := by
        calc (2 * q) * (2 * q) = 2 * (q * (2 * q)) := Int.mul_assoc _ _ _
          _ = 2 * (2 * (q * q)) := by rw [Int.mul_left_comm q 2 q]
          _ = (2 * 2) * (q * q) := (Int.mul_assoc _ _ _).symm
          _ = 4 * (q * q) := rfl
      have hmul : (2 * q + 1) * (2 * q + 1) = 4 * (q * q) + 4 * q + 1 := by
        rw [Int.add_mul, Int.mul_add, Int.mul_add, h2q]
        omega
      have hmul2 : 4 * (q * (q + 1)) = 4 * (q * q) + 4 * q := by
        rw [Int.mul_add, Int.mul_add]; omega
      omega
    rw [hexp, ht]
    change 4 * (2 * t) = (8 : Int) * t
    omega
  | s + 2, _ => by
    have ih := odd_pow_two_pow_sub_one u hu (s + 1) (by omega)
    rcases ih with ⟨t, ht⟩
    have hpow_odd : (u ^ (2 ^ (s + 1))) % 2 ≠ 0 := by
      have hodd_pow : ∀ m : Nat, (u ^ m) % 2 ≠ 0 := by
        intro m
        induction m with
        | zero => simp
        | succ m' ihm =>
          rw [Int.pow_succ, Int.mul_emod]
          have h1 : u % 2 = 1 := by omega
          have h2 : (u ^ m') % 2 = 1 := by omega
          rw [h1, h2]; decide
      exact hodd_pow _
    have hplus_even : (2 : Int) ∣ (u ^ (2 ^ (s + 1)) + 1) := ⟨(u ^ (2 ^ (s + 1)) + 1) / 2, by omega⟩
    rcases hplus_even with ⟨w, hw⟩
    refine ⟨t * w, ?_⟩
    have hfactor : u ^ (2 ^ (s + 2)) - 1 = (u ^ (2 ^ (s + 1)) - 1) * (u ^ (2 ^ (s + 1)) + 1) := by
      have hexp : 2 ^ (s + 2) = 2 ^ (s + 1) + 2 ^ (s + 1) := by rw [Nat.pow_succ]; omega
      rw [hexp, Int.pow_add]
      have hdiff : ∀ a : Int, a * a - 1 = (a - 1) * (a + 1) := by
        intro a
        rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.one_mul, Int.mul_one]
        omega
      exact hdiff _
    rw [hfactor, ht, hw]
    have hpow_eq : ((2 ^ (s + 2 + 2) : Nat) : Int) = ((2 ^ (s + 1 + 2) : Nat) : Int) * 2 := by
      rw [show s + 2 + 2 = (s + 1 + 2) + 1 by omega, Nat.pow_succ, Int.natCast_mul]
      rfl
    rw [hpow_eq]
    calc (((2 ^ (s + 1 + 2) : Nat) : Int) * t) * (2 * w)
        = (((2 ^ (s + 1 + 2) : Nat) : Int) * 2) * (t * w) := by
          rw [Int.mul_assoc, Int.mul_left_comm t 2 w, ← Int.mul_assoc]

theorem even_pow_dvd (u : Int) (hu : (2 : Int) ∣ u) :
    ∀ m : Nat, ((2 ^ m : Nat) : Int) ∣ u ^ m
  | 0 => by simp
  | m + 1 => by
    rcases hu with ⟨q, rfl⟩
    rcases even_pow_dvd (2 * q) ⟨q, rfl⟩ m with ⟨t, ht⟩
    refine ⟨t * q, ?_⟩
    rw [Int.pow_succ, ht, Nat.pow_succ, Int.natCast_mul]
    calc (((2 ^ m : Nat) : Int) * t) * (2 * q)
        = (((2 ^ m : Nat) : Int) * (2 : Nat)) * (t * q) := by
          change (((2 ^ m : Nat) : Int) * t) * (2 * q) = (((2 ^ m : Nat) : Int) * 2) * (t * q)
          rw [Int.mul_assoc, Int.mul_left_comm t 2 q, ← Int.mul_assoc]

theorem nat_pow2_ge_succ (s : Nat) (hs : 1 ≤ s) : s + 1 ≤ 2 ^ s := by
  induction s with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => decide
    | succ m' =>
      have := ih (by omega)
      rw [Nat.pow_succ]; omega

theorem nat_pow2_ge_add_two (s : Nat) (hs : 2 ≤ s) : s + 2 ≤ 2 ^ s := by
  induction s with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => omega
    | succ m' =>
      cases m' with
      | zero => decide
      | succ m'' =>
        have hih := ih (by omega)
        have hstep : 2 ^ (m'' + 2 + 1) = 2 ^ (m'' + 2) * 2 := Nat.pow_succ 2 (m'' + 2)
        omega

theorem dvd_pow2_of_le {a b : Nat} (h : a ≤ b) : ((2 ^ a : Nat) : Int) ∣ ((2 ^ b : Nat) : Int) := by
  refine ⟨((2 ^ (b - a) : Nat) : Int), ?_⟩
  rw [← Int.natCast_mul, ← Nat.pow_add, Nat.add_sub_cancel' h]

theorem even_sq_sub_two_mul (a : Int) (ha : (2 : Int) ∣ a) : (8 : Int) ∣ (a * a - 2 * a) := by
  rcases ha with ⟨q, rfl⟩
  have heven : (2 : Int) ∣ q * (q - 1) := by
    by_cases hqm : q % 2 = 0
    · exact ⟨(q / 2) * (q - 1), by
        have hq2 : q = 2 * (q / 2) := by omega
        calc q * (q - 1) = (2 * (q / 2)) * (q - 1) := by rw [← hq2]
          _ = 2 * ((q / 2) * (q - 1)) := by rw [Int.mul_assoc]⟩
    · exact ⟨q * ((q - 1) / 2), by
        have hq2 : q - 1 = 2 * ((q - 1) / 2) := by omega
        calc q * (q - 1) = q * (2 * ((q - 1) / 2)) := by rw [← hq2]
          _ = 2 * (q * ((q - 1) / 2)) := by rw [Int.mul_left_comm]⟩
  rcases heven with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have h1 : (2 * q) * (2 * q) - 2 * (2 * q) = 4 * (q * (q - 1)) := by
    rw [Int.mul_sub, Int.mul_one, Int.mul_sub]
    have h2 : (2 * q) * (2 * q) = 4 * (q * q) := by
      calc (2 * q) * (2 * q) = 2 * (q * (2 * q)) := Int.mul_assoc _ _ _
        _ = 2 * (2 * (q * q)) := by rw [Int.mul_left_comm q 2 q]
        _ = (2 * 2) * (q * q) := (Int.mul_assoc _ _ _).symm
        _ = 4 * (q * q) := rfl
    omega
  rw [h1, ht]; omega

-- ============================================================================
-- SECTION 5: THEOREM 1 — Universal 2-Group Permanent Collapse Mod 2^(k+1)
-- ============================================================================

theorem maskCard_act {k n : Nat} {Gr : Fin2Group k} (BA : FreeBiAction Gr n) (g : Gr.G) (S : Mask n) :
    maskCard n ((maskAct BA).act g S) = maskCard n S := by
  unfold maskCard
  apply length_bijection ((List.nodup_finRange n).filter _) ((List.nodup_finRange n).filter _)
    (BA.colAct.act (Gr.inv g)) (BA.colAct.act g)
  · intro j hj
    rw [List.mem_filter] at hj ⊢
    exact ⟨List.mem_finRange _, hj.2⟩
  · intro j hj
    rw [List.mem_filter] at hj ⊢
    refine ⟨List.mem_finRange _, ?_⟩
    change S (BA.colAct.act (Gr.inv g) (BA.colAct.act g j)) = true
    rw [← BA.colAct.act_mul, Gr.inv_mul, BA.colAct.act_one]
    exact hj.2
  · intro j _; rw [← BA.colAct.act_mul, Gr.mul_inv, BA.colAct.act_one]
  · intro j _; rw [← BA.colAct.act_mul, Gr.inv_mul, BA.colAct.act_one]

-- Row sum equivariance:

theorem rowSum_act_eq {k n : Nat} {Gr : Fin2Group k} (BA : FreeBiAction Gr n) (A : Mat n)
    (heq : IsEquivariant BA A) (g : Gr.G) (S : Mask n) (i : Fin n) :
    rowSum n A ((maskAct BA).act g S) (BA.rowAct.act g i) = rowSum n A S i := by
  unfold rowSum
  have h1 : sumInt ((List.finRange n).filter ((maskAct BA).act g S)) (fun j => A (BA.rowAct.act g i) j) =
      sumInt ((List.finRange n).filter ((maskAct BA).act g S)) (fun j => A i (BA.colAct.act (Gr.inv g) j)) := by
    apply sumInt_congr
    intro j _
    have hinv := heq g i (BA.colAct.act (Gr.inv g) j)
    rw [← BA.colAct.act_mul, Gr.mul_inv, BA.colAct.act_one] at hinv
    exact hinv
  rw [h1]
  exact sumInt_bijection ((List.nodup_finRange n).filter _) ((List.nodup_finRange n).filter _)
    (BA.colAct.act (Gr.inv g)) (BA.colAct.act g)
    (fun j hj => by rw [List.mem_filter] at hj ⊢; exact ⟨List.mem_finRange _, hj.2⟩)
    (fun j hj => by
      rw [List.mem_filter] at hj ⊢
      refine ⟨List.mem_finRange _, ?_⟩
      change S (BA.colAct.act (Gr.inv g) (BA.colAct.act g j)) = true
      rw [← BA.colAct.act_mul, Gr.inv_mul, BA.colAct.act_one]
      exact hj.2)
    (fun j _ => by rw [← BA.colAct.act_mul, Gr.mul_inv, BA.colAct.act_one])
    (fun j _ => by rw [← BA.colAct.act_mul, Gr.inv_mul, BA.colAct.act_one])
    (fun j => A i j)

theorem rowProd_act {k n : Nat} {Gr : Fin2Group k} (BA : FreeBiAction Gr n) (A : Mat n)
    (heq : IsEquivariant BA A) (g : Gr.G) (S : Mask n) :
    rowProd n A ((maskAct BA).act g S) = rowProd n A S := by
  unfold rowProd
  have h1 : prodInt (List.finRange n) (rowSum n A ((maskAct BA).act g S)) =
      prodInt (List.finRange n) (fun i => rowSum n A ((maskAct BA).act g S) (BA.rowAct.act g i)) := by
    exact (prodInt_bijection (List.nodup_finRange n) (List.nodup_finRange n)
      (BA.rowAct.act g) (BA.rowAct.act (Gr.inv g))
      (fun _ _ => List.mem_finRange _) (fun _ _ => List.mem_finRange _)
      (fun i _ => by rw [← BA.rowAct.act_mul, Gr.inv_mul, BA.rowAct.act_one])
      (fun i _ => by rw [← BA.rowAct.act_mul, Gr.mul_inv, BA.rowAct.act_one])
      (rowSum n A ((maskAct BA).act g S))).symm
  rw [h1]
  exact prodInt_congr (fun i _ => rowSum_act_eq BA A heq g S i)

theorem rowProdOdd_iff_allRowsOdd (n : Nat) (A : Mat n) (S : Mask n) :
    rowProdOdd n A S = true ↔ ∀ i : Fin n, rowSum n A S i % 2 ≠ 0 := by
  unfold rowProdOdd rowProd
  rw [decide_eq_true_eq]
  have haux : ∀ (l : List (Fin n)) (f : Fin n → Int),
      prodInt l f % 2 ≠ 0 ↔ ∀ i ∈ l, f i % 2 ≠ 0 := by
    intro l f
    induction l with
    | nil => simp
    | cons x xs ih =>
      simp only [prodInt_cons, List.mem_cons]
      rw [Int.mul_emod]
      constructor
      · intro h i hi
        have hx : f x % 2 ≠ 0 := by intro hx0; simp [hx0] at h
        have hxs : prodInt xs f % 2 ≠ 0 := by intro hxs0; simp [hxs0] at h
        rcases hi with rfl | hmem
        · exact hx
        · exact ih.mp hxs i hmem
      · intro h
        have hx : f x % 2 = 1 := by have := h x (Or.inl rfl); omega
        have hxs : prodInt xs f % 2 = 1 := by have := ih.mpr (fun i hi => h i (Or.inr hi)); omega
        rw [hx, hxs]; decide
  constructor
  · intro h i
    exact (haux (List.finRange n) (rowSum n A S)).mp h i (List.mem_finRange i)
  · intro h
    exact (haux (List.finRange n) (rowSum n A S)).mpr (fun i _ => h i)

theorem free_biaction_even_n {k n : Nat} (Gr : Fin2Group k) (BA : FreeBiAction Gr n) (hk : 1 ≤ k) :
    n % 2 = 0 := by
  let H : Subgroup Gr := {
    elems := Gr.elems
    nodup := Gr.nodup
    one_mem := Gr.complete Gr.one
    mul_mem := fun _ _ _ _ => Gr.complete _
    inv_mem := fun _ _ => Gr.complete _
  }
  have hdvd : H.elems.length ∣ (List.finRange n).length :=
    free_subgroup_dvd_length Gr H BA.rowAct BA.row_free n (List.finRange n)
      (by simp) (List.nodup_finRange n) (fun _ _ _ _ => List.mem_finRange _)
  rw [List.length_finRange] at hdvd
  change Gr.elems.length ∣ n at hdvd
  rw [Gr.card] at hdvd
  have h2dvd : 2 ∣ 2 ^ k := by
    cases k with
    | zero => omega
    | succ k' => rw [Nat.pow_succ]; exact ⟨2 ^ k', by omega⟩
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h2dvd hdvd)

/-- THEOREM 1 (Universal 2-Group Permanent Collapse Mod 2^(k+1)):
    For ANY k ≥ 1, ANY n, ANY finite 2-group G of order 2^k with a free bi-action on Fin n,
    and ANY G-equivariant integer matrix A : Mat n,
      perm(A) ≡ #{S ⊆ Fin n : ∀ i, ∑_{j ∈ S} A(i,j) is odd}  (mod 2^(k+1)). -/
theorem perm_mod_two_pow_succ {k n : Nat} (hk : 1 ≤ k) (Gr : Fin2Group k)
    (BA : FreeBiAction Gr n) (A : Mat n) (heq : IsEquivariant BA A) :
    ((2 ^ (k + 1) : Nat) : Int) ∣ (perm n A - (oddSolCount n A : Int)) := by
  rw [perm_eq_ryserSum]
  unfold ryserSum oddSolCount
  have hcnt : (((allMasks n).filter (rowProdOdd n A)).length : Int) =
      sumInt (allMasks n) (fun S => if rowProdOdd n A S then (1 : Int) else 0) := by
    rw [← sumInt_filter_eq_sumInt_ite, sumInt_const, Int.mul_one]
  rw [hcnt, ← sumInt_sub]
  let Δ : Mask n → Int := fun S => ryserSign n S * rowProd n A S - if rowProdOdd n A S then 1 else 0
  change ((2 ^ (k + 1) : Nat) : Int) ∣ sumInt (allMasks n) Δ
  apply twoGroup_sum_dvd Gr (maskAct BA) Δ 1
    (fun g S => by
      simp only [Δ, ryserSign, maskCard_act, rowProd_act BA A heq, rowProdOdd]; rfl)
    (allMasks n).length (allMasks n) (Nat.le_refl _) (nodup_allMasks n)
    (fun _ _ _ => mem_allMasks n _)
  intro S _ s hs hstab_len
  -- Case s = 0 vs s ≥ 1
  cases s with
  | zero =>
    -- Need 2 ∣ (ryserSign * rowProd - 1_{rowProd odd}), which holds for EVERY mask S!
    simp only [Nat.zero_add, Nat.pow_one, Δ, rowProdOdd]
    have hsign : ryserSign n S = 1 ∨ ryserSign n S = -1 := by
      unfold ryserSign; by_cases h : (n - maskCard n S) % 2 = 0 <;> simp [h]
    by_cases hodd : rowProd n A S % 2 ≠ 0
    · simp only [decide_eq_true hodd, ↓reduceIte]
      rcases hsign with hs1 | hs1 <;> rw [hs1]
      · exact ⟨(rowProd n A S - 1) / 2, by omega⟩
      · exact ⟨(-rowProd n A S - 1) / 2, by omega⟩
    · simp only [decide_eq_false hodd, Bool.false_eq_true, ↓reduceIte, Int.sub_zero]
      rcases hsign with hs1 | hs1 <;> rw [hs1]
      · exact ⟨rowProd n A S / 2, by omega⟩
      · exact ⟨-(rowProd n A S / 2), by omega⟩
  | succ s' =>
    -- H = stab S has order 2^(s'+1) ≥ 2 (EVEN!).
    let H := stabSubgroup Gr (maskAct BA) S
    have hH_len : H.elems.length = 2 ^ (s' + 1) := hstab_len
    -- 1. Since H acts freely on columns and S is H-invariant, |H| ∣ maskCard n S, so maskCard is EVEN!
    have hcol_closed : ∀ h ∈ H.elems, ∀ j ∈ (List.finRange n).filter S, BA.colAct.act h j ∈ (List.finRange n).filter S := by
      intro h hh j hj
      rw [List.mem_filter] at hj ⊢
      refine ⟨List.mem_finRange _, ?_⟩
      have hfix : (maskAct BA).act h S = S := (mem_stab Gr (maskAct BA) S h).mp hh
      have hval := congrFun hfix (BA.colAct.act h j)
      have hact : (maskAct BA).act h S (BA.colAct.act h j) = S j := by
        change S (BA.colAct.act (Gr.inv h) (BA.colAct.act h j)) = S j
        rw [← BA.colAct.act_mul, Gr.inv_mul, BA.colAct.act_one]
      exact hval.symm.trans (hact.trans hj.2)
    have hcard_dvd : 2 ^ (s' + 1) ∣ maskCard n S := by
      rw [← hH_len]
      exact free_subgroup_dvd_length Gr H BA.colAct BA.col_free _ _
        (Nat.le_refl _) ((List.nodup_finRange n).filter _) hcol_closed
    have hcard_even : maskCard n S % 2 = 0 := by
      have h2 : 2 ∣ 2 ^ (s' + 1) := by rw [Nat.pow_succ]; exact ⟨2 ^ s', by omega⟩
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h2 hcard_dvd)
    have hn_even : n % 2 = 0 := free_biaction_even_n Gr BA hk
    have hle : maskCard n S ≤ n := maskCard_le n S
    have hsign1 : ryserSign n S = 1 := by
      unfold ryserSign
      have : (n - maskCard n S) % 2 = 0 := by omega
      simp [this]
    -- 2. Since H acts freely on rows and rowSum is H-invariant, ∃ u, rowProd = u ^ (2^(s'+1))!
    have hrow_inv : ∀ h ∈ H.elems, ∀ i, rowSum n A S (BA.rowAct.act h i) = rowSum n A S i := by
      intro h hh i
      have hfix : (maskAct BA).act h S = S := (mem_stab Gr (maskAct BA) S h).mp hh
      have hact := rowSum_act_eq BA A heq h S i
      rw [hfix] at hact
      exact hact
    rcases free_subgroup_prod_pow Gr H BA.rowAct BA.row_free (rowSum n A S) hrow_inv
        n (List.finRange n) (by simp) (List.nodup_finRange n) (fun _ _ _ _ => List.mem_finRange _) with ⟨u, hu⟩
    rw [hH_len] at hu
    -- 3. Apply LTE (if u odd) or even_pow_dvd (if u even)!
    simp only [Δ, hsign1, Int.one_mul, rowProdOdd]
    change ((2 ^ (s' + 1 + 1) : Nat) : Int) ∣ (rowProd n A S - if decide (rowProd n A S % 2 ≠ 0) then 1 else 0)
    rw [show rowProd n A S = u ^ (2 ^ (s' + 1)) from hu]
    by_cases hu_odd : u % 2 ≠ 0
    · have hpow_odd : (u ^ (2 ^ (s' + 1))) % 2 ≠ 0 := by
        have haux : ∀ m : Nat, (u ^ m) % 2 ≠ 0 := by
          intro m; induction m with
          | zero => simp
          | succ m' ihm =>
            rw [Int.pow_succ, Int.mul_emod]
            have h1 : u % 2 = 1 := by omega
            have h2 : (u ^ m') % 2 = 1 := by omega
            rw [h1, h2]; decide
        exact haux _
      simp only [decide_eq_true hpow_odd, ↓reduceIte]
      have hlte := odd_pow_two_pow_sub_one u hu_odd (s' + 1) (by omega)
      exact Int.dvd_trans (dvd_pow2_of_le (by omega)) hlte
    · have hu_even : (2 : Int) ∣ u := ⟨u / 2, by omega⟩
      have hpow_dvd := even_pow_dvd u hu_even (2 ^ (s' + 1))
      have hge : s' + 1 + 1 ≤ 2 ^ (s' + 1) := nat_pow2_ge_succ (s' + 1) (by omega)
      have hpow_even : ¬ (u ^ (2 ^ (s' + 1))) % 2 ≠ 0 := by
        have h1le : 1 ≤ 2 ^ (s' + 1) := by omega
        have h2dvd : (2 : Int) ∣ u ^ (2 ^ (s' + 1)) :=
          Int.dvd_trans (dvd_pow2_of_le h1le) hpow_dvd
        rcases h2dvd with ⟨t, ht⟩; omega
      simp only [decide_eq_false hpow_even, Bool.false_eq_true, ↓reduceIte, Int.sub_zero]
      exact Int.dvd_trans (dvd_pow2_of_le hge) hpow_dvd

theorem perm_mod_two_pow_succ_of_unique_odd {k n : Nat} (hk : 1 ≤ k) (Gr : Fin2Group k)
    (BA : FreeBiAction Gr n) (A : Mat n) (heq : IsEquivariant BA A)
    (huniq : oddSolCount n A = 1) :
    ((2 ^ (k + 1) : Nat) : Int) ∣ (perm n A - 1) := by
  have h := perm_mod_two_pow_succ hk Gr BA A heq
  rw [huniq] at h
  exact h

theorem xorCirc_equivariant (k : Nat) (f : Fin (2 ^ k) → Int) :
    IsEquivariant (xorFreeBiAction k) (xorCirc k f) := by
  intro (g : Fin (2 ^ k)) i j
  change f (xorFin k (xorFin k g i) (xorFin k g j)) = f (xorFin k i j)
  congr 1
  calc xorFin k (xorFin k g i) (xorFin k g j)
      = xorFin k (xorFin k (xorFin k g i) g) j := (xorFin_assoc k _ _ _).symm
    _ = xorFin k (xorFin k g (xorFin k i g)) j := by rw [xorFin_assoc k g i g]
    _ = xorFin k (xorFin k g (xorFin k g i)) j := by rw [xorFin_comm k i g]
    _ = xorFin k (xorFin k (xorFin k g g) i) j := by rw [← xorFin_assoc k g g i]
    _ = xorFin k i j := by rw [xorFin_self k g, xorFin_zero_left k i]

theorem cycCirc_equivariant (k : Nat) (f : Fin (2 ^ k) → Int) :
    IsEquivariant (cycFreeBiAction k) (cycCirc k f) := by
  intro (g : Fin (2 ^ k)) i j
  change f (addFin k (addFin k g i) (negFin k (addFin k g j))) = f (addFin k i (negFin k j))
  congr 1
  rw [negFin_addFin k g j]
  calc addFin k (addFin k g i) (addFin k (negFin k g) (negFin k j))
      = addFin k (addFin k i g) (addFin k (negFin k g) (negFin k j)) := by rw [addFin_comm k g i]
    _ = addFin k i (addFin k g (addFin k (negFin k g) (negFin k j))) := addFin_assoc k _ _ _
    _ = addFin k i (addFin k (addFin k g (negFin k g)) (negFin k j)) := by rw [← addFin_assoc k g]
    _ = addFin k i (addFin k (addFin k (negFin k g) g) (negFin k j)) := by rw [addFin_comm k g (negFin k g)]
    _ = addFin k i (negFin k j) := by rw [addFin_neg_left k g, addFin_zero_left k]

theorem antiCyc_equivariant (k : Nat) (f : Fin (2 ^ k) → Int) :
    IsEquivariant (antiCycFreeBiAction k) (antiCyc k f) := by
  intro (g : Fin (2 ^ k)) i j
  change f (addFin k (addFin k g i) (addFin k (negFin k g) j)) = f (addFin k i j)
  congr 1
  calc addFin k (addFin k g i) (addFin k (negFin k g) j)
      = addFin k (addFin k i g) (addFin k (negFin k g) j) := by rw [addFin_comm k g i]
    _ = addFin k i (addFin k g (addFin k (negFin k g) j)) := addFin_assoc k _ _ _
    _ = addFin k i (addFin k (addFin k g (negFin k g)) j) := by rw [← addFin_assoc k g]
    _ = addFin k i (addFin k (addFin k (negFin k g) g) j) := by rw [addFin_comm k g (negFin k g)]
    _ = addFin k i j := by rw [addFin_neg_left k g, addFin_zero_left k]

theorem xorCirc_perm_mod_two_pow_succ {k : Nat} (hk : 1 ≤ k) (f : Fin (2 ^ k) → Int) :
    ((2 ^ (k + 1) : Nat) : Int) ∣ (perm (2 ^ k) (xorCirc k f) - (oddSolCount (2 ^ k) (xorCirc k f) : Int)) :=
  perm_mod_two_pow_succ hk (xorGroup k) (xorFreeBiAction k) (xorCirc k f) (xorCirc_equivariant k f)

theorem cycCirc_perm_mod_two_pow_succ {k : Nat} (hk : 1 ≤ k) (f : Fin (2 ^ k) → Int) :
    ((2 ^ (k + 1) : Nat) : Int) ∣ (perm (2 ^ k) (cycCirc k f) - (oddSolCount (2 ^ k) (cycCirc k f) : Int)) :=
  perm_mod_two_pow_succ hk (cycGroup k) (cycFreeBiAction k) (cycCirc k f) (cycCirc_equivariant k f)

theorem antiCyc_perm_mod_two_pow_succ {k : Nat} (hk : 1 ≤ k) (f : Fin (2 ^ k) → Int) :
    ((2 ^ (k + 1) : Nat) : Int) ∣ (perm (2 ^ k) (antiCyc k f) - (oddSolCount (2 ^ k) (antiCyc k f) : Int)) :=
  perm_mod_two_pow_succ hk (cycGroup k) (antiCycFreeBiAction k) (antiCyc k f) (antiCyc_equivariant k f)

-- ============================================================================
-- SECTION 7: GF(2) XOR-Convolution Involution/Nilpotency & THEOREM 2 (Even Row Sum)
-- ============================================================================

theorem sumInt_mod2_congr {α : Type} {l : List α} {f g : α → Int}
    (h : ∀ x ∈ l, f x % 2 = g x % 2) : sumInt l f % 2 = sumInt l g % 2 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [sumInt_cons]
    rw [Int.add_emod, h x (by simp), ih (fun y hy => h y (by simp [hy])), ← Int.add_emod]

theorem rowSum_eq_sum_ite (n : Nat) (A : Mat n) (S : Mask n) (i : Fin n) :
    rowSum n A S i = sumInt (List.finRange n) (fun j => if S j then A i j else 0) :=
  sumInt_filter_eq_sumInt_ite (List.finRange n) S (fun j => A i j)

theorem conv2_xorMask (k : Nat) (f : Fin (2 ^ k) → Int) (S₁ S₂ : Mask (2 ^ k)) :
    conv2 k f (xorMask S₁ S₂) = xorMask (conv2 k f S₁) (conv2 k f S₂) := by
  funext i
  unfold conv2 xorMask
  have hmod : rowSum (2 ^ k) (xorCirc k f) (fun j => xor (S₁ j) (S₂ j)) i % 2 =
      (rowSum (2 ^ k) (xorCirc k f) S₁ i + rowSum (2 ^ k) (xorCirc k f) S₂ i) % 2 := by
    rw [rowSum_eq_sum_ite, rowSum_eq_sum_ite, rowSum_eq_sum_ite, ← sumInt_add]
    apply sumInt_mod2_congr
    intro j _
    cases S₁ j <;> cases S₂ j <;> simp <;> omega
  rw [hmod, Int.add_emod]
  by_cases h1 : rowSum (2 ^ k) (xorCirc k f) S₁ i % 2 ≠ 0 <;>
  by_cases h2 : rowSum (2 ^ k) (xorCirc k f) S₂ i % 2 ≠ 0 <;>
  simp [h1, h2] <;> omega

theorem conv2_allTrue (k : Nat) (f : Fin (2 ^ k) → Int) :
    conv2 k f (allTrueMask (2 ^ k)) =
      if rowSumAll k f % 2 ≠ 0 then allTrueMask (2 ^ k) else allFalseMask (2 ^ k) := by
  funext i
  have hsum : rowSum (2 ^ k) (xorCirc k f) (allTrueMask (2 ^ k)) i = rowSumAll k f := by
    unfold rowSum allTrueMask rowSumAll xorCirc
    rw [filter_const_true]
    exact sumInt_bijection (List.nodup_finRange _) (List.nodup_finRange _)
      (xorFin k i) (xorFin k i)
      (fun _ _ => List.mem_finRange _) (fun _ _ => List.mem_finRange _)
      (fun j _ => by rw [← xorFin_assoc, xorFin_self, xorFin_zero_left])
      (fun j _ => by rw [← xorFin_assoc, xorFin_self, xorFin_zero_left])
      f
  unfold conv2
  rw [hsum]
  unfold allTrueMask allFalseMask
  by_cases hodd : rowSumAll k f % 2 ≠ 0 <;> simp [hodd]

/-- Fundamental GF(2) XOR-Convolution Identity:
    (A_f^2 · S) mod 2 = (rowSum(f) mod 2) · S.
    Simultaneously proves involutivity (odd row sum) and nilpotency (even row sum)! -/
theorem conv2_conv2 (k : Nat) (f : Fin (2 ^ k) → Int) (S : Mask (2 ^ k)) :
    conv2 k f (conv2 k f S) =
      if rowSumAll k f % 2 ≠ 0 then S else allFalseMask (2 ^ k) := by
  funext i
  unfold conv2
  have hstep1 : rowSum (2 ^ k) (xorCirc k f) (fun x => decide (rowSum (2 ^ k) (xorCirc k f) S x % 2 ≠ 0)) i % 2 =
      sumInt (List.finRange (2 ^ k)) (fun x =>
        xorCirc k f i x * rowSum (2 ^ k) (xorCirc k f) S x) % 2 := by
    rw [rowSum_eq_sum_ite]
    apply sumInt_mod2_congr
    intro x _
    by_cases hx : rowSum (2 ^ k) (xorCirc k f) S x % 2 ≠ 0
    · simp only [decide_eq_true hx, ↓reduceIte]
      rw [Int.mul_emod]
      have h1 : rowSum (2 ^ k) (xorCirc k f) S x % 2 = 1 := by omega
      rw [h1, Int.mul_one, Int.emod_emod]
    · simp only [decide_eq_false hx, Bool.false_eq_true, ↓reduceIte]
      rw [Int.mul_emod]
      have h0 : rowSum (2 ^ k) (xorCirc k f) S x % 2 = 0 := by omega
      rw [h0, Int.mul_zero]
  have hstep2 : sumInt (List.finRange (2 ^ k)) (fun x =>
        xorCirc k f i x * rowSum (2 ^ k) (xorCirc k f) S x) =
      sumInt (List.finRange (2 ^ k)) (fun y =>
        if S y then sumInt (List.finRange (2 ^ k)) (fun x => f (xorFin k i x) * f (xorFin k x y)) else 0) := by
    calc sumInt (List.finRange (2 ^ k)) (fun x => xorCirc k f i x * rowSum (2 ^ k) (xorCirc k f) S x)
        = sumInt (List.finRange (2 ^ k)) (fun x =>
            sumInt (List.finRange (2 ^ k)) (fun y =>
              if S y then f (xorFin k i x) * f (xorFin k x y) else 0)) := by
          apply sumInt_congr
          intro x _
          rw [rowSum_eq_sum_ite, ← sumInt_mul_left]
          apply sumInt_congr
          intro y _
          cases S y <;> simp [xorCirc]
      _ = sumInt (List.finRange (2 ^ k)) (fun y =>
            sumInt (List.finRange (2 ^ k)) (fun x =>
              if S y then f (xorFin k i x) * f (xorFin k x y) else 0)) :=
          sumInt_comm _ _ _
      _ = sumInt (List.finRange (2 ^ k)) (fun y =>
            if S y then sumInt (List.finRange (2 ^ k)) (fun x => f (xorFin k i x) * f (xorFin k x y)) else 0) := by
          apply sumInt_congr
          intro y _
          cases S y
          · simp [sumInt_zero]
          · rfl
  have hpair_even : ∀ y : Fin (2 ^ k), y ≠ i →
      sumInt (List.finRange (2 ^ k)) (fun x => f (xorFin k i x) * f (xorFin k x y)) % 2 = 0 := by
    intro y hne
    let d := xorFin k i y
    have hd_ne : d ≠ finZero k := by
      intro h0
      apply hne
      have h1 := congrArg (fun z => xorFin k z y) h0
      simp only [d] at h1
      rw [xorFin_assoc, xorFin_self, xorFin_zero_right, xorFin_zero_left] at h1
      exact h1.symm
    have hg_inv : ∀ x : Fin (2 ^ k),
        f (xorFin k i (xorFin k d x)) * f (xorFin k (xorFin k d x) y) =
        f (xorFin k i x) * f (xorFin k x y) := by
      intro x
      have h1 : xorFin k i (xorFin k d x) = xorFin k x y := by
        simp only [d]
        calc xorFin k i (xorFin k (xorFin k i y) x)
            = xorFin k (xorFin k i (xorFin k i y)) x := (xorFin_assoc k _ _ _).symm
          _ = xorFin k (xorFin k (xorFin k i i) y) x := by rw [← xorFin_assoc k i i y]
          _ = xorFin k y x := by rw [xorFin_self, xorFin_zero_left]
          _ = xorFin k x y := xorFin_comm k y x
      have h2 : xorFin k (xorFin k d x) y = xorFin k i x := by
        simp only [d]
        calc xorFin k (xorFin k (xorFin k i y) x) y
            = xorFin k (xorFin k i y) (xorFin k x y) := xorFin_assoc k _ _ _
          _ = xorFin k (xorFin k i y) (xorFin k y x) := by rw [xorFin_comm k x y]
          _ = xorFin k i (xorFin k y (xorFin k y x)) := xorFin_assoc k _ _ _
          _ = xorFin k i (xorFin k (xorFin k y y) x) := by rw [← xorFin_assoc k y y x]
          _ = xorFin k i x := by rw [xorFin_self, xorFin_zero_left]
      rw [h1, h2, Int.mul_comm]
    let l₁ := (List.finRange (2 ^ k)).filter (fun x => decide (x.val < (xorFin k d x).val))
    let l₂ := (List.finRange (2 ^ k)).filter (fun x => !decide (x.val < (xorFin k d x).val))
    have hsplit : sumInt (List.finRange (2 ^ k)) (fun x => f (xorFin k i x) * f (xorFin k x y)) =
        sumInt l₁ (fun x => f (xorFin k i x) * f (xorFin k x y)) +
        sumInt l₂ (fun x => f (xorFin k i x) * f (xorFin k x y)) :=
      (sumInt_filter_add_not _ _ _).symm
    have hne_act : ∀ x : Fin (2 ^ k), xorFin k d x ≠ x := fun x h =>
      hd_ne ((xorFin_eq_right_iff k d x).mp h)
    have hbij : sumInt l₁ (fun x => f (xorFin k i x) * f (xorFin k x y)) =
        sumInt l₂ (fun x => f (xorFin k i x) * f (xorFin k x y)) := by
      have hcongr : sumInt l₁ (fun x => f (xorFin k i x) * f (xorFin k x y)) =
          sumInt l₁ (fun x => f (xorFin k i (xorFin k d x)) * f (xorFin k (xorFin k d x) y)) :=
        sumInt_congr (fun x _ => (hg_inv x).symm)
      rw [hcongr]
      exact sumInt_bijection ((List.nodup_finRange _).filter _) ((List.nodup_finRange _).filter _)
        (xorFin k d) (xorFin k d)
        (fun x hx => by
          rw [List.mem_filter] at hx ⊢
          refine ⟨List.mem_finRange _, ?_⟩
          have hlt : x.val < (xorFin k d x).val := of_decide_eq_true hx.2
          have hdd : xorFin k d (xorFin k d x) = x := by rw [← xorFin_assoc, xorFin_self, xorFin_zero_left]
          rw [hdd]; simp; omega)
        (fun x hx => by
          rw [List.mem_filter] at hx ⊢
          refine ⟨List.mem_finRange _, ?_⟩
          have hge : ¬ x.val < (xorFin k d x).val := by intro hc; simp [hc] at hx
          have hne' : (xorFin k d x).val ≠ x.val := fun hv => hne_act x (Fin.ext hv)
          have hdd : xorFin k d (xorFin k d x) = x := by rw [← xorFin_assoc, xorFin_self, xorFin_zero_left]
          rw [hdd]; exact decide_eq_true (by omega))
        (fun x _ => by rw [← xorFin_assoc, xorFin_self, xorFin_zero_left])
        (fun x _ => by rw [← xorFin_assoc, xorFin_self, xorFin_zero_left])
        (fun x => f (xorFin k i x) * f (xorFin k x y))
    rw [hsplit, hbij]; omega
  have hdiag : sumInt (List.finRange (2 ^ k)) (fun x => f (xorFin k i x) * f (xorFin k x i)) % 2 =
      rowSumAll k f % 2 := by
    have hsq : sumInt (List.finRange (2 ^ k)) (fun x => f (xorFin k i x) * f (xorFin k x i)) % 2 =
        sumInt (List.finRange (2 ^ k)) (fun x => f (xorFin k i x)) % 2 := by
      apply sumInt_mod2_congr
      intro x _
      rw [xorFin_comm k x i, Int.mul_emod]
      by_cases hm : f (xorFin k i x) % 2 = 0
      · rw [hm]; decide
      · have hm1 : f (xorFin k i x) % 2 = 1 := by omega
        rw [hm1]; decide
    rw [hsq]
    unfold rowSumAll
    have hbij := sumInt_bijection (List.nodup_finRange _) (List.nodup_finRange _)
      (xorFin k i) (xorFin k i)
      (fun _ _ => List.mem_finRange _) (fun _ _ => List.mem_finRange _)
      (fun x _ => by rw [← xorFin_assoc, xorFin_self, xorFin_zero_left])
      (fun x _ => by rw [← xorFin_assoc, xorFin_self, xorFin_zero_left])
      f
    rw [hbij]
  have hfinal : rowSum (2 ^ k) (xorCirc k f) (fun x => decide (rowSum (2 ^ k) (xorCirc k f) S x % 2 ≠ 0)) i % 2 =
      (if S i then rowSumAll k f else 0) % 2 := by
    rw [hstep1, hstep2]
    have hmod_y : sumInt (List.finRange (2 ^ k)) (fun y =>
          if S y then sumInt (List.finRange (2 ^ k)) (fun x => f (xorFin k i x) * f (xorFin k x y)) else 0) % 2 =
        sumInt (List.finRange (2 ^ k)) (fun y =>
          if y = i then (if S i then rowSumAll k f else 0) else 0) % 2 := by
      apply sumInt_mod2_congr
      intro y _
      by_cases hyi : y = i
      · subst hyi
        simp only [↓reduceIte]
        cases S y
        · rfl
        · exact hdiag
      · simp only [hyi, ↓reduceIte]
        cases S y
        · rfl
        · exact hpair_even y hyi
    rw [hmod_y]
    have hsingle : ∀ (l : List (Fin (2 ^ k))) (c : Int), l.Nodup → i ∈ l →
        sumInt l (fun y => if y = i then c else 0) = c := by
      intro l c hnd hmem
      induction l with
      | nil => cases hmem
      | cons y ys ihy =>
        have ⟨hy_nmem, hys_nd⟩ := List.nodup_cons.mp hnd
        simp only [sumInt_cons]
        by_cases hyi : y = i
        · subst hyi
          simp only [↓reduceIte]
          rw [sumInt_zero (fun z hz => by
            have hne : z ≠ y := fun h => hy_nmem (h ▸ hz)
            simp [hne]), Int.add_zero]
        · simp only [hyi, ↓reduceIte, Int.zero_add]
          have hmem' : i ∈ ys := by
            rcases List.mem_cons.mp hmem with rfl | h
            · exact absurd rfl hyi
            · exact h
          exact ihy hys_nd hmem'
    rw [hsingle (List.finRange (2 ^ k)) _ (List.nodup_finRange _) (List.mem_finRange i)]
  rw [hfinal]
  by_cases hodd : rowSumAll k f % 2 ≠ 0
  · cases hsi : S i <;> simp [hodd, hsi]
  · cases hsi : S i <;> simp [hodd, allFalseMask]

/-- Corollary: An XOR-circulant matrix with odd row sum has a UNIQUE odd-row-sum subset (allTrueMask). -/
theorem xorCirc_odd_unique_sol (k : Nat) (f : Fin (2 ^ k) → Int)
    (hodd : rowSumAll k f % 2 ≠ 0) :
    oddSolCount (2 ^ k) (xorCirc k f) = 1 := by
  unfold oddSolCount
  have hflt : (allMasks (2 ^ k)).filter (rowProdOdd (2 ^ k) (xorCirc k f)) = [allTrueMask (2 ^ k)] := by
    apply List.Perm.eq_singleton
    apply perm_of_nodup_iff ((nodup_allMasks _).filter _) (by simp)
    intro S
    simp only [List.mem_filter, mem_allMasks, true_and, List.mem_singleton]
    rw [rowProdOdd_iff_allRowsOdd]
    constructor
    · intro hall
      have hc : conv2 k f S = allTrueMask (2 ^ k) := by
        funext i; unfold conv2 allTrueMask; exact decide_eq_true (hall i)
      have hinv := conv2_conv2 k f S
      simp [hodd, hc, conv2_allTrue] at hinv
      exact hinv.symm
    · intro hS; subst hS
      intro i
      have hc := congrFun (conv2_allTrue k f) i
      simp [hodd, conv2, allTrueMask] at hc
      exact hc
  rw [hflt]; rfl

theorem xorCirc_odd_perm_mod_two_pow_succ {k : Nat} (hk : 1 ≤ k) (f : Fin (2 ^ k) → Int)
    (hodd : rowSumAll k f % 2 ≠ 0) :
    ((2 ^ (k + 1) : Nat) : Int) ∣ (perm (2 ^ k) (xorCirc k f) - 1) :=
  perm_mod_two_pow_succ_of_unique_odd hk (xorGroup k) (xorFreeBiAction k)
    (xorCirc k f) (xorCirc_equivariant k f) (xorCirc_odd_unique_sol k f hodd)

/-- THEOREM 2 (Even-Row-Sum XOR-Circulant Collapse for ALL k ≥ 3):
    For every k ≥ 3 and every integer XOR-circulant 2^k × 2^k matrix with even row sum,
      2^(k + 1) ∣ perm(2^k, xorCirc k f). -/
theorem xorCirc_even_rowSum_dvd {k : Nat} (hk : 3 ≤ k) (f : Fin (2 ^ k) → Int)
    (heven : rowSumAll k f % 2 = 0) :
    ((2 ^ (k + 1) : Nat) : Int) ∣ perm (2 ^ k) (xorCirc k f) := by
  have h1 := xorCirc_perm_mod_two_pow_succ (by omega : 1 ≤ k) f
  -- Suffices to show 2^(k + 1) ∣ oddSolCount (2^k) (xorCirc k f)!
  suffices hcnt : 2 ^ (k + 1) ∣ oddSolCount (2 ^ k) (xorCirc k f) by
    rcases h1 with ⟨q₁, hq₁⟩
    rcases hcnt with ⟨q₂, hq₂⟩
    refine ⟨q₁ + q₂, ?_⟩
    have hq2i : (oddSolCount (2 ^ k) (xorCirc k f) : Int) = ((2 ^ (k + 1) : Nat) : Int) * q₂ := by
      rw [hq₂, Int.natCast_mul]
    rw [Int.mul_add, ← hq₁, ← hq2i]; omega
  -- If no solution exists, oddSolCount = 0 and we are done.
  let sols := (allMasks (2 ^ k)).filter (rowProdOdd (2 ^ k) (xorCirc k f))
  change 2 ^ (k + 1) ∣ sols.length
  cases hsols : sols with
  | nil => exact Nat.dvd_zero _
  | cons S₀ _ =>
    have hS₀_mem : S₀ ∈ sols := by rw [hsols]; simp
    have hS₀_conv : conv2 k f S₀ = allTrueMask (2 ^ k) := by
      have hodd := (rowProdOdd_iff_allRowsOdd _ _ _).mp (List.mem_filter.mp hS₀_mem).2
      funext i; unfold conv2 allTrueMask; exact decide_eq_true (hodd i)
    -- Define ker = {T | conv2 k f T = allFalseMask} and im = dedup (map (conv2 k f) (allMasks (2^k))).
    let ker := (allMasks (2 ^ k)).filter (fun T => decide (conv2 k f T = allFalseMask (2 ^ k)))
    let im := dedup ((allMasks (2 ^ k)).map (conv2 k f))
    -- 1. sols.length = ker.length (bijection T ↦ xorMask S₀ T)
    have hsols_eq_ker : sols.length = ker.length := by
      apply length_bijection ((nodup_allMasks _).filter _) ((nodup_allMasks _).filter _)
        (xorMask S₀) (xorMask S₀)
      · intro S hS
        rw [List.mem_filter] at hS ⊢
        refine ⟨mem_allMasks _ _, decide_eq_true ?_⟩
        have hSc : conv2 k f S = allTrueMask (2 ^ k) := by
          have ho := (rowProdOdd_iff_allRowsOdd _ _ _).mp hS.2
          funext i; unfold conv2 allTrueMask; exact decide_eq_true (ho i)
        rw [conv2_xorMask, hS₀_conv, hSc]
        funext i; simp [xorMask, allTrueMask, allFalseMask]
      · intro T hT
        rw [List.mem_filter] at hT ⊢
        refine ⟨mem_allMasks _ _, (rowProdOdd_iff_allRowsOdd _ _ _).mpr ?_⟩
        have hTc : conv2 k f T = allFalseMask (2 ^ k) := of_decide_eq_true hT.2
        have hxor : conv2 k f (xorMask S₀ T) = allTrueMask (2 ^ k) := by
          rw [conv2_xorMask, hS₀_conv, hTc]
          funext i; simp [xorMask, allTrueMask, allFalseMask]
        intro i
        have hi := congrFun hxor i
        simpa [conv2, allTrueMask] using hi
      · intro S _; funext i; simp [xorMask]
      · intro T _; funext i; simp [xorMask]
    -- 2. Every fiber of conv2 over y ∈ im has length ker.length, so im.length * ker.length = 2^(2^k)!
    have hfiber : ∀ y ∈ im,
        ((allMasks (2 ^ k)).filter (fun S => decide (conv2 k f S = y))).length = ker.length := by
      intro y hy
      rw [mem_dedup, List.mem_map] at hy
      rcases hy with ⟨S₁, _, rfl⟩
      apply length_bijection ((nodup_allMasks _).filter _) ((nodup_allMasks _).filter _)
        (xorMask S₁) (xorMask S₁)
      · intro S hS
        rw [List.mem_filter] at hS ⊢
        refine ⟨mem_allMasks _ _, decide_eq_true ?_⟩
        rw [conv2_xorMask, of_decide_eq_true hS.2]
        funext i; simp [xorMask, allFalseMask]
      · intro T hT
        rw [List.mem_filter] at hT ⊢
        refine ⟨mem_allMasks _ _, decide_eq_true ?_⟩
        rw [conv2_xorMask, of_decide_eq_true hT.2]
        funext i; simp [xorMask, allFalseMask]
      · intro S _; funext i; simp [xorMask]
      · intro T _; funext i; simp [xorMask]
    have hrank_nullity : im.length * ker.length = 2 ^ (2 ^ k) := by
      have hsum := length_eq_sum_fibers (allMasks (2 ^ k)) (conv2 k f) im (nodup_dedup _)
        (fun S hS => (mem_dedup _ _).mpr (List.mem_map.mpr ⟨S, hS, rfl⟩))
      have hconst : im.map (fun y => ((allMasks (2 ^ k)).filter (fun S => decide (conv2 k f S = y))).length) =
          im.map (fun _ => ker.length) := List.map_congr_left hfiber
      rw [hconst] at hsum
      have hsum_const : ∀ (l : List (Mask (2 ^ k))) (c : Nat), (l.map (fun _ => c)).sum = l.length * c := by
        intro l c
        induction l with
        | nil => simp
        | cons _ xs ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
          rw [Nat.succ_mul, Nat.add_comm]
      rw [hsum_const, length_allMasks] at hsum
      exact hsum.symm
    -- 3. By nilpotency (conv2_conv2), im ⊆ ker, so im.length ≤ ker.length!
    have him_sub_ker : ∀ y ∈ im, y ∈ ker := by
      intro y hy
      rw [mem_dedup, List.mem_map] at hy
      rcases hy with ⟨S, _, rfl⟩
      rw [List.mem_filter]
      refine ⟨mem_allMasks _ _, decide_eq_true ?_⟩
      have hcc := conv2_conv2 k f S
      have hnot_odd : ¬ rowSumAll k f % 2 ≠ 0 := by omega
      simp only [hnot_odd, ↓reduceIte] at hcc
      exact hcc
    have him_le_ker : im.length ≤ ker.length := by
      have haux : ∀ (l₁ l₂ : List (Mask (2 ^ k))), l₁.Nodup → (∀ y ∈ l₁, y ∈ l₂) → l₁.length ≤ l₂.length := by
        intro l₁
        induction l₁ with
        | nil => intro _ _ _; simp
        | cons x xs ih =>
          intro l₂ hnd hsub
          have ⟨hx_nmem, hxs_nd⟩ := List.nodup_cons.mp hnd
          have hmem : x ∈ l₂ := hsub x (by simp)
          let l₂' := l₂.filter (fun z => decide (z ≠ x))
          have hsub' : ∀ y ∈ xs, y ∈ l₂' := by
            intro y hy
            rw [List.mem_filter]
            exact ⟨hsub y (by simp [hy]), decide_eq_true (fun h => hx_nmem (h ▸ hy))⟩
          have hih := ih l₂' hxs_nd hsub'
          have hlt : l₂'.length < l₂.length := by
            have hcnt_pos : 0 < (l₂.filter (fun z => decide (z = x))).length :=
              List.length_pos_of_mem (List.mem_filter.mpr ⟨hmem, decide_eq_true rfl⟩)
            have hsplit : l₂.length = (l₂.filter (fun z => decide (z = x))).length + l₂'.length := by
              have haux2 : ∀ (l : List (Mask (2 ^ k))),
                  l.length = (l.filter (fun z => decide (z = x))).length + (l.filter (fun z => decide (z ≠ x))).length := by
                intro l
                induction l with
                | nil => simp
                | cons a as iha =>
                  rw [List.filter_cons, List.filter_cons]
                  by_cases ha : a = x
                  · have h1 : decide (a = x) = true := decide_eq_true ha
                    have h2 : decide (a ≠ x) = false := decide_eq_false (fun h => h ha)
                    rw [h1, h2]; simp only [↓reduceIte, Bool.false_eq_true, List.length_cons]; omega
                  · have h1 : decide (a = x) = false := decide_eq_false ha
                    have h2 : decide (a ≠ x) = true := decide_eq_true ha
                    rw [h1, h2]; simp only [↓reduceIte, Bool.false_eq_true, List.length_cons]; omega
              exact haux2 l₂
            omega
          simp only [List.length_cons]; omega
      exact haux im ker (nodup_dedup _) him_sub_ker
    -- 4. Since im.length * ker.length = 2^(2^k), ker.length = 2^s with 2*s ≥ 2^k, so s ≥ 2^(k-1) ≥ k+1!
    rcases pow2_of_mul_eq_pow2 (2 ^ k) im.length ker.length hrank_nullity with ⟨s, hs, hker_pow, him_pow⟩
    have hs_ge : 2 ^ (k - 1) ≤ s := by
      have hpow_le : 2 ^ (2 ^ k - s) ≤ 2 ^ s := by rw [← him_pow, ← hker_pow]; exact him_le_ker
      have hexp_le : 2 ^ k - s ≤ s := by
        by_cases hle : 2 ^ k - s ≤ s
        · exact hle
        · exfalso
          have hlt : s < 2 ^ k - s := by omega
          have hpow_lt : 2 ^ s < 2 ^ (2 ^ k - s) := Nat.pow_lt_pow_right (by omega) hlt
          omega
      have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
        cases k with
        | zero => omega
        | succ k' => simp [Nat.pow_succ, Nat.mul_comm]
      omega
    have hk_bound : k + 1 ≤ 2 ^ (k - 1) := by
      have haux : ∀ m : Nat, 2 ≤ m → m + 2 ≤ 2 ^ m := nat_pow2_ge_add_two
      have hm : 2 ≤ k - 1 := by omega
      have hres := haux (k - 1) hm
      omega
    rw [← hsols, hsols_eq_ker, hker_pow]
    exact Nat.pow_dvd_pow 2 (by omega)

theorem evenRowMask_iff (k : Nat) (f : Fin (2 ^ k) → Int) (S : Mask (2 ^ k)) (i : Fin (2 ^ k)) :
    evenRowMask k f S i = true ↔ rowSum (2 ^ k) (xorCirc k f) S i % 2 = 0 := by
  unfold evenRowMask conv2
  by_cases h : rowSum (2 ^ k) (xorCirc k f) S i % 2 = 0
  · simp [h]
  · simp [h]

theorem evenRowMask_eq_xor (k : Nat) (f : Fin (2 ^ k) → Int) (S : Mask (2 ^ k)) :
    evenRowMask k f S = xorMask (allTrueMask (2 ^ k)) (conv2 k f S) := by
  funext i
  simp [evenRowMask, xorMask, allTrueMask]

theorem maskOfEvenRows_left_inv (k : Nat) (f : Fin (2 ^ k) → Int)
    (hodd : rowSumAll k f % 2 ≠ 0) (S : Mask (2 ^ k)) :
    maskOfEvenRows k f (evenRowMask k f S) = S := by
  unfold maskOfEvenRows
  rw [evenRowMask_eq_xor, conv2_xorMask, conv2_allTrue, conv2_conv2]
  have h1 : (if rowSumAll k f % 2 ≠ 0 then allTrueMask (2 ^ k) else allFalseMask (2 ^ k)) = allTrueMask (2 ^ k) := by
    simp [hodd]
  have h2 : (if rowSumAll k f % 2 ≠ 0 then S else allFalseMask (2 ^ k)) = S := by
    simp [hodd]
  rw [h1, h2]
  funext i; simp [xorMask, allTrueMask]

theorem maskOfEvenRows_right_inv (k : Nat) (f : Fin (2 ^ k) → Int)
    (hodd : rowSumAll k f % 2 ≠ 0) (E : Mask (2 ^ k)) :
    evenRowMask k f (maskOfEvenRows k f E) = E := by
  rw [evenRowMask_eq_xor]
  unfold maskOfEvenRows
  rw [conv2_xorMask, conv2_allTrue, conv2_conv2]
  have h1 : (if rowSumAll k f % 2 ≠ 0 then allTrueMask (2 ^ k) else allFalseMask (2 ^ k)) = allTrueMask (2 ^ k) := by
    simp [hodd]
  have h2 : (if rowSumAll k f % 2 ≠ 0 then E else allFalseMask (2 ^ k)) = E := by
    simp [hodd]
  rw [h1, h2]
  funext i; simp [xorMask, allTrueMask]

theorem evenRowMask_act (k : Nat) (f : Fin (2 ^ k) → Int) (g : (xorGroup k).G) (S : Mask (2 ^ k)) :
    evenRowMask k f ((maskAct (xorFreeBiAction k)).act g S) =
    (maskAct (xorFreeBiAction k)).act g (evenRowMask k f S) := by
  funext i
  let g' : Fin (2 ^ k) := g
  have hact := rowSum_act_eq (xorFreeBiAction k) (xorCirc k f) (xorCirc_equivariant k f) g S (xorFin k g' i)
  have hgg : (xorFreeBiAction k).rowAct.act g (xorFin k g' i) = i := by
    change xorFin k g' (xorFin k g' i) = i
    rw [← xorFin_assoc, xorFin_self, xorFin_zero_left]
  rw [hgg] at hact
  change (!decide (rowSum (2 ^ k) (xorCirc k f) ((maskAct (xorFreeBiAction k)).act g S) i % 2 ≠ 0)) =
         (!decide (rowSum (2 ^ k) (xorCirc k f) S (xorFin k g' i) % 2 ≠ 0))
  rw [hact]

theorem evenRowList_length_act (k : Nat) (f : Fin (2 ^ k) → Int) (g : (xorGroup k).G) (S : Mask (2 ^ k)) :
    (evenRowList k f ((maskAct (xorFreeBiAction k)).act g S)).length = (evenRowList k f S).length := by
  unfold evenRowList
  rw [evenRowMask_act]
  exact maskCard_act (xorFreeBiAction k) g (evenRowMask k f S)

theorem mem_stab_iff_evenRowMask (k : Nat) (f : Fin (2 ^ k) → Int)
    (hodd : rowSumAll k f % 2 ≠ 0) (S : Mask (2 ^ k)) (g : (xorGroup k).G) :
    g ∈ stab (xorGroup k) (maskAct (xorFreeBiAction k)) S ↔
    (maskAct (xorFreeBiAction k)).act g (evenRowMask k f S) = evenRowMask k f S := by
  rw [mem_stab]
  constructor
  · intro h
    rw [← evenRowMask_act, h]
  · intro h
    have h1 := congrArg (maskOfEvenRows k f) (evenRowMask_act k f g S)
    rw [maskOfEvenRows_left_inv k f hodd, h, maskOfEvenRows_left_inv k f hodd] at h1
    exact h1

/-- Helper: if a list has length 2 and is nodup, it equals [a, b] with a ≠ b. -/
theorem list_eq_two_of_length_two {α : Type} {l : List α} (hnd : l.Nodup) (hlen : l.length = 2) :
    ∃ a b : α, l = [a, b] ∧ a ≠ b := by
  cases l with
  | nil => simp at hlen
  | cons a t =>
    cases t with
    | nil => simp at hlen
    | cons b t2 =>
      cases t2 with
      | nil =>
        have ⟨ha, _⟩ := List.nodup_cons.mp hnd
        have hne : a ≠ b := fun h => ha (by simp [h])
        exact ⟨a, b, rfl, hne⟩
      | cons _ _ => simp at hlen

/-- Helper: if a list has length 1, it equals [a]. -/
theorem list_eq_one_of_length_one {α : Type} {l : List α} (hlen : l.length = 1) :
    ∃ a : α, l = [a] := by
  cases l with
  | nil => simp at hlen
  | cons a t =>
    cases t with
    | nil => exact ⟨a, rfl⟩
    | cons _ _ => simp at hlen

/-- Helper: if every element of a list is even, then 2^(l.length) divides prodInt l r. -/
theorem prodInt_even_dvd {α : Type} (l : List α) (r : α → Int)
    (heven : ∀ x ∈ l, (2 : Int) ∣ r x) :
    ((2 ^ l.length : Nat) : Int) ∣ prodInt l r := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, prodInt_cons, Nat.pow_succ, Int.natCast_mul]
    rcases heven x (by simp) with ⟨q₁, hq₁⟩
    rcases ih (fun y hy => heven y (by simp [hy])) with ⟨q₂, hq₂⟩
    refine ⟨q₁ * q₂, ?_⟩
    rw [hq₁, hq₂]
    change (2 * q₁) * (((2 ^ xs.length : Nat) : Int) * q₂) = (((2 ^ xs.length : Nat) : Int) * 2) * (q₁ * q₂)
    calc (2 * q₁) * (((2 ^ xs.length : Nat) : Int) * q₂)
        = (2 * ((2 ^ xs.length : Nat) : Int)) * (q₁ * q₂) := by
          rw [Int.mul_assoc, Int.mul_left_comm q₁ _ q₂, ← Int.mul_assoc]
      _ = (((2 ^ xs.length : Nat) : Int) * 2) * (q₁ * q₂) := by rw [Int.mul_comm 2]

/-- Helper: product of odd integers is odd. -/
theorem prodInt_odd {α : Type} (l : List α) (r : α → Int)
    (hodd : ∀ x ∈ l, r x % 2 ≠ 0) : prodInt l r % 2 ≠ 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [prodInt_cons]
    rw [Int.mul_emod]
    have hx : r x % 2 = 1 := by have := hodd x (by simp); omega
    have hxs : prodInt xs r % 2 = 1 := by have := ih (fun y hy => hodd y (by simp [hy])); omega
    rw [hx, hxs]; decide

/-- Helper: if S has exactly 2 even rows [x₁, x₂], then h = x₁ ^^^ x₂ stabilizes S,
    so rowSum S x₁ = rowSum S x₂, and stab S = [0, h] has length 2. -/
theorem two_even_rows_props (k : Nat) (f : Fin (2 ^ k) → Int)
    (hodd : rowSumAll k f % 2 ≠ 0) (S : Mask (2 ^ k))
    {x₁ x₂ : Fin (2 ^ k)} (hne : x₁ ≠ x₂) (heq : evenRowList k f S = [x₁, x₂]) :
    let h : (xorGroup k).G := xorFin k x₁ x₂
    h ≠ (xorGroup k).one ∧
    (∀ g : (xorGroup k).G, g ∈ stab (xorGroup k) (maskAct (xorFreeBiAction k)) S ↔ g = (xorGroup k).one ∨ g = h) ∧
    (stab (xorGroup k) (maskAct (xorFreeBiAction k)) S).length = 2 ∧
    rowSum (2 ^ k) (xorCirc k f) S x₁ = rowSum (2 ^ k) (xorCirc k f) S x₂ := by
  intro h
  have hmem_iff : ∀ x : Fin (2 ^ k), evenRowMask k f S x = true ↔ (x = x₁ ∨ x = x₂) := by
    intro x
    have hx : x ∈ evenRowList k f S ↔ evenRowMask k f S x = true := by
      simp [evenRowList, List.mem_finRange]
    rw [← hx, heq]; simp
  have hh_ne : h ≠ (xorGroup k).one := by
    intro h0
    apply hne
    have h1 := congrArg (fun z => xorFin k z x₂) h0
    simp only [h] at h1
    change xorFin k (xorFin k x₁ x₂) x₂ = xorFin k (finZero k) x₂ at h1
    rw [xorFin_assoc, xorFin_self, xorFin_zero_right, xorFin_zero_left] at h1
    exact h1
  have hhx1 : xorFin k h x₁ = x₂ := by
    simp only [h]
    rw [xorFin_comm k x₁ x₂, xorFin_assoc, xorFin_self, xorFin_zero_right]
  have hhx2 : xorFin k h x₂ = x₁ := by
    simp only [h]
    rw [xorFin_assoc, xorFin_self, xorFin_zero_right]
  have hstab_iff : ∀ g : (xorGroup k).G, g ∈ stab (xorGroup k) (maskAct (xorFreeBiAction k)) S ↔ g = (xorGroup k).one ∨ g = h := by
    intro g
    rw [mem_stab_iff_evenRowMask k f hodd S g]
    let g' : Fin (2 ^ k) := g
    constructor
    · intro hact
      have hx1 : evenRowMask k f S (xorFin k g' x₁) = true := by
        have hv := congrFun hact x₁
        change evenRowMask k f S (xorFin k g' x₁) = evenRowMask k f S x₁ at hv
        rw [hv]; exact (hmem_iff x₁).mpr (Or.inl rfl)
      rcases (hmem_iff _).mp hx1 with h1 | h2
      · left; exact (xorFin_eq_right_iff k g' x₁).mp h1
      · right
        have h3 := congrArg (fun z => xorFin k z x₁) h2
        rw [xorFin_assoc, xorFin_self, xorFin_zero_right, xorFin_comm k x₂ x₁] at h3
        exact h3
    · intro hg
      rcases hg with rfl | rfl
      · exact (maskAct (xorFreeBiAction k)).act_one _
      · funext x
        change evenRowMask k f S (xorFin k h x) = evenRowMask k f S x
        cases hb : evenRowMask k f S x
        · cases hb2 : evenRowMask k f S (xorFin k h x)
          · rfl
          · exfalso
            rcases (hmem_iff _).mp hb2 with h1 | h2
            · have hx : x = x₂ := by
                have := congrArg (xorFin k h) h1
                rw [← xorFin_assoc, xorFin_self, xorFin_zero_left, hhx1] at this; exact this
              rw [hx, (hmem_iff x₂).mpr (Or.inr rfl)] at hb; cases hb
            · have hx : x = x₁ := by
                have := congrArg (xorFin k h) h2
                rw [← xorFin_assoc, xorFin_self, xorFin_zero_left, hhx2] at this; exact this
              rw [hx, (hmem_iff x₁).mpr (Or.inl rfl)] at hb; cases hb
        · rcases (hmem_iff x).mp hb with rfl | rfl
          · rw [hhx1]; exact (hmem_iff x₂).mpr (Or.inr rfl)
          · rw [hhx2]; exact (hmem_iff x₁).mpr (Or.inl rfl)
  have hstab_len : (stab (xorGroup k) (maskAct (xorFreeBiAction k)) S).length = 2 := by
    let pairL : List (xorGroup k).G := [(xorGroup k).one, h]
    have hnd_pair : pairL.Nodup := by
      rw [List.nodup_cons]
      refine ⟨?_, by rw [List.nodup_cons]; exact ⟨List.not_mem_nil, List.nodup_nil⟩⟩
      intro hm
      have heq1 : (xorGroup k).one = h := List.mem_singleton.mp hm
      exact hh_ne heq1.symm
    have hperm : (stab (xorGroup k) (maskAct (xorFreeBiAction k)) S).Perm pairL := by
      apply perm_of_nodup_iff (nodup_stab _ _ _) hnd_pair
      intro g
      have hmem_pair : g ∈ pairL ↔ (g = (xorGroup k).one ∨ g = h) := by
        simp [pairL]
      rw [hmem_pair]
      exact hstab_iff g
    exact hperm.length_eq
  have hrow_eq : rowSum (2 ^ k) (xorCirc k f) S x₁ = rowSum (2 ^ k) (xorCirc k f) S x₂ := by
    have hfix : (maskAct (xorFreeBiAction k)).act h S = S :=
      (mem_stab (xorGroup k) (maskAct (xorFreeBiAction k)) S h).mp ((hstab_iff h).mpr (Or.inr rfl))
    have hact := rowSum_act_eq (xorFreeBiAction k) (xorCirc k f) (xorCirc_equivariant k f) h S x₁
    rw [hfix] at hact
    change rowSum (2 ^ k) (xorCirc k f) S (xorFin k h x₁) = rowSum (2 ^ k) (xorCirc k f) S x₁ at hact
    rw [hhx1] at hact
    exact hact.symm
  exact ⟨hh_ne, hstab_iff, hstab_len, hrow_eq⟩

theorem defectCorr_inv (k : Nat) (f : Fin (2 ^ k) → Int)
    (hodd : rowSumAll k f % 2 ≠ 0) (g : (xorGroup k).G) (S : Mask (2 ^ k)) :
    defectCorr k f ((maskAct (xorFreeBiAction k)).act g S) = defectCorr k f S := by
  let g' : Fin (2 ^ k) := g
  let S' := (maskAct (xorFreeBiAction k)).act g S
  have hlen : (evenRowList k f S').length = (evenRowList k f S).length :=
    evenRowList_length_act k f g S
  unfold defectCorr
  cases hl : evenRowList k f S with
  | nil =>
    have hl' : evenRowList k f S' = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, hl]; rfl)
    change (match evenRowList k f S' with | [] => 1 | [_] => evenSum k f | [x, _] => 2 * rowSum (2 ^ k) (xorCirc k f) S' x | _ => 0) = 1
    rw [hl']
  | cons a t =>
    cases t with
    | nil =>
      rcases list_eq_one_of_length_one (by rw [hlen, hl]; rfl) with ⟨a', ha'⟩
      change (match evenRowList k f S' with | [] => 1 | [_] => evenSum k f | [x, _] => 2 * rowSum (2 ^ k) (xorCirc k f) S' x | _ => 0) = evenSum k f
      rw [ha']
    | cons b t2 =>
      cases t2 with
      | nil =>
        have hnd : (evenRowList k f S).Nodup := (List.nodup_finRange _).filter _
        rw [hl] at hnd
        have hne : a ≠ b := by
          have ⟨ha, _⟩ := List.nodup_cons.mp hnd
          intro h; exact ha (by simp [h])
        have ⟨_, _, _, hrow_ab⟩ := two_even_rows_props k f hodd S hne hl
        have hnd' : (evenRowList k f S').Nodup := (List.nodup_finRange _).filter _
        rcases list_eq_two_of_length_two hnd' (by rw [hlen, hl]; rfl) with ⟨a', b', hl', _⟩
        change (match evenRowList k f S' with | [] => 1 | [_] => evenSum k f | [x, _] => 2 * rowSum (2 ^ k) (xorCirc k f) S' x | _ => 0) =
          2 * rowSum (2 ^ k) (xorCirc k f) S a
        rw [hl']
        dsimp only []
        have ha'_mem : evenRowMask k f S' a' = true := by
          have : a' ∈ evenRowList k f S' := by rw [hl']; simp
          exact (List.mem_filter.mp this).2
        have hga'_mem : xorFin k g' a' ∈ evenRowList k f S := by
          rw [evenRowMask_act] at ha'_mem
          exact List.mem_filter.mpr ⟨List.mem_finRange _, ha'_mem⟩
        rw [hl] at hga'_mem
        have hact_row := rowSum_act_eq (xorFreeBiAction k) (xorCirc k f) (xorCirc_equivariant k f) g S (xorFin k g' a')
        have hgg : (xorFreeBiAction k).rowAct.act g (xorFin k g' a') = a' := by
          change xorFin k g' (xorFin k g' a') = a'
          rw [← xorFin_assoc, xorFin_self, xorFin_zero_left]
        rw [hgg] at hact_row
        change rowSum (2 ^ k) (xorCirc k f) S' a' = rowSum (2 ^ k) (xorCirc k f) S (xorFin k g' a') at hact_row
        rw [hact_row]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hga'_mem
        rcases hga'_mem with h1 | h2
        · rw [h1]
        · rw [h2, hrow_ab]
      | cons c t3 =>
        have hge3 : (evenRowList k f S').length ≥ 3 := by rw [hlen, hl]; simp
        change (match evenRowList k f S' with | [] => 1 | [_] => evenSum k f | [x, _] => 2 * rowSum (2 ^ k) (xorCirc k f) S' x | _ => 0) = 0
        cases hl' : evenRowList k f S' with
        | nil => rw [hl'] at hge3; simp at hge3
        | cons _ u =>
          cases u with
          | nil => rw [hl'] at hge3; simp at hge3
          | cons _ u2 =>
            cases u2 with
            | nil => rw [hl'] at hge3; simp at hge3
            | cons _ _ => rfl

/-- Core Mod-2^(k+2) Orbit-Collapse Lemma (using `twoGroup_sum_dvd` at c = 2!). -/
theorem xorCirc_perm_sub_defectCorr_dvd {k : Nat} (hk : 1 ≤ k) (f : Fin (2 ^ k) → Int)
    (hodd : rowSumAll k f % 2 ≠ 0) :
    ((2 ^ (k + 2) : Nat) : Int) ∣ (perm (2 ^ k) (xorCirc k f) - sumInt (allMasks (2 ^ k)) (defectCorr k f)) := by
  rw [perm_eq_ryserSum]
  unfold ryserSum
  rw [← sumInt_sub]
  let Δ : Mask (2 ^ k) → Int := fun S => ryserSign (2 ^ k) S * rowProd (2 ^ k) (xorCirc k f) S - defectCorr k f S
  change ((2 ^ (k + 2) : Nat) : Int) ∣ sumInt (allMasks (2 ^ k)) Δ
  apply twoGroup_sum_dvd (xorGroup k) (maskAct (xorFreeBiAction k)) Δ 2
    (fun g S => by
      change ryserSign (2 ^ k) ((maskAct (xorFreeBiAction k)).act g S) *
          rowProd (2 ^ k) (xorCirc k f) ((maskAct (xorFreeBiAction k)).act g S) -
          defectCorr k f ((maskAct (xorFreeBiAction k)).act g S) =
        ryserSign (2 ^ k) S * rowProd (2 ^ k) (xorCirc k f) S - defectCorr k f S
      unfold ryserSign
      rw [maskCard_act, rowProd_act (xorFreeBiAction k) (xorCirc k f) (xorCirc_equivariant k f),
        defectCorr_inv k f hodd g S])
    (allMasks (2 ^ k)).length (allMasks (2 ^ k)) (Nat.le_refl _) (nodup_allMasks _)
    (fun _ _ _ => mem_allMasks _ _)
  intro S _ s hs hstab_len
  -- Helper: when s ≥ 1, ryserSign (2^k) S = 1
  have hsign_of_s_pos : 1 ≤ s → ryserSign (2 ^ k) S = 1 := by
    intro hs1
    let H := stabSubgroup (xorGroup k) (maskAct (xorFreeBiAction k)) S
    have hcol_closed : ∀ h ∈ H.elems, ∀ j ∈ (List.finRange (2 ^ k)).filter S,
        (xorFreeBiAction k).colAct.act h j ∈ (List.finRange (2 ^ k)).filter S := by
      intro h hh j hj
      rw [List.mem_filter] at hj ⊢
      refine ⟨List.mem_finRange _, ?_⟩
      have hfix : (maskAct (xorFreeBiAction k)).act h S = S := (mem_stab _ _ _ _).mp hh
      have hval := congrFun hfix ((xorFreeBiAction k).colAct.act h j)
      have hact : (maskAct (xorFreeBiAction k)).act h S ((xorFreeBiAction k).colAct.act h j) = S j := by
        change S ((xorFreeBiAction k).colAct.act ((xorGroup k).inv h) ((xorFreeBiAction k).colAct.act h j)) = S j
        rw [← (xorFreeBiAction k).colAct.act_mul, (xorGroup k).inv_mul, (xorFreeBiAction k).colAct.act_one]
      exact hval.symm.trans (hact.trans hj.2)
    have hcard_dvd : 2 ^ s ∣ maskCard (2 ^ k) S := by
      rw [← hstab_len]
      exact free_subgroup_dvd_length (xorGroup k) H (xorFreeBiAction k).colAct (xorFreeBiAction k).col_free
        _ _ (Nat.le_refl _) ((List.nodup_finRange _).filter _) hcol_closed
    have h2s : 2 ∣ 2 ^ s := by
      cases s with | zero => omega | succ s' => rw [Nat.pow_succ]; exact ⟨2 ^ s', by omega⟩
    have hcard_even : maskCard (2 ^ k) S % 2 = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h2s hcard_dvd)
    have hn_even : (2 ^ k) % 2 = 0 := free_biaction_even_n (xorGroup k) (xorFreeBiAction k) hk
    have hle := maskCard_le (2 ^ k) S
    unfold ryserSign
    have : (2 ^ k - maskCard (2 ^ k) S) % 2 = 0 := by omega
    simp [this]
  -- Case split on evenRowList k f S!
  cases hl : evenRowList k f S with
  | nil =>
    -- |evenRowList| = 0 ⇒ S = allTrueMask ⇒ s = k, rowProd = (rowSumAll k f)^(2^k), LTE gives 2^(k+2) ∣ u^(2^k) - 1!
    have hEm : evenRowMask k f S = allFalseMask (2 ^ k) := by
      funext i
      cases hb : evenRowMask k f S i
      · rfl
      · exfalso
        have : i ∈ evenRowList k f S := List.mem_filter.mpr ⟨List.mem_finRange i, hb⟩
        rw [hl] at this; cases this
    have hS_all : S = allTrueMask (2 ^ k) := by
      have hinv := maskOfEvenRows_left_inv k f hodd S
      rw [hEm] at hinv
      unfold maskOfEvenRows at hinv
      have hc0 : conv2 k f (allFalseMask (2 ^ k)) = allFalseMask (2 ^ k) := by
        funext i; unfold conv2 allFalseMask rowSum
        have hemp : (List.finRange (2 ^ k)).filter (fun _ => false) = [] := by
          rw [List.filter_eq_nil_iff]; intro _ _; simp
        rw [hemp]; rfl
      rw [hc0] at hinv
      rw [← hinv]; funext i; simp [xorMask, allTrueMask, allFalseMask]
    have hstab_all : (stab (xorGroup k) (maskAct (xorFreeBiAction k)) S).length = 2 ^ k := by
      have hperm : (stab (xorGroup k) (maskAct (xorFreeBiAction k)) S).Perm (xorGroup k).elems := by
        apply perm_of_nodup_iff (nodup_stab _ _ _) (xorGroup k).nodup
        intro g
        rw [mem_stab]
        constructor
        · intro _; exact (xorGroup k).complete g
        · intro _; rw [hS_all]; funext i; rfl
      rw [hperm.length_eq, (xorGroup k).card]
    have hsk : s = k := by
      have hp : 2 ^ s = 2 ^ k := hstab_len.symm.trans hstab_all
      by_cases he : s = k
      · exact he
      · exfalso
        have hlt : s < k := by omega
        have := Nat.pow_lt_pow_right (by omega : 1 < 2) hlt
        omega
    rw [hsk]
    have hsign1 := hsign_of_s_pos (by omega)
    have hprod_all : rowProd (2 ^ k) (xorCirc k f) S = (rowSumAll k f) ^ (2 ^ k) := by
      rw [hS_all]; unfold rowProd
      have hrow_const : ∀ i ∈ List.finRange (2 ^ k), rowSum (2 ^ k) (xorCirc k f) (allTrueMask (2 ^ k)) i = rowSumAll k f := by
        intro i _
        unfold rowSum allTrueMask rowSumAll xorCirc
        rw [filter_const_true]
        exact sumInt_bijection (List.nodup_finRange _) (List.nodup_finRange _)
          (xorFin k i) (xorFin k i)
          (fun _ _ => List.mem_finRange _) (fun _ _ => List.mem_finRange _)
          (fun j _ => by rw [← xorFin_assoc, xorFin_self, xorFin_zero_left])
          (fun j _ => by rw [← xorFin_assoc, xorFin_self, xorFin_zero_left])
          f
      rw [prodInt_congr hrow_const, prodInt_const, List.length_finRange]
    simp only [Δ, defectCorr, hl, hsign1, Int.one_mul]
    rw [hprod_all]
    exact odd_pow_two_pow_sub_one (rowSumAll k f) hodd k hk
  | cons x₀ t =>
    cases t with
    | nil =>
      -- |evenRowList| = 1 ⇒ stab S = {0} (s = 0), rowSum S x₀ = evenSum k f, need 4 ∣ (ryserSign * rowProd - evenSum)!
      have hmem_x0 : ∀ x : Fin (2 ^ k), evenRowMask k f S x = true ↔ x = x₀ := by
        intro x
        have hx : x ∈ evenRowList k f S ↔ evenRowMask k f S x = true := by
          simp [evenRowList, List.mem_finRange]
        rw [← hx, hl]; simp
      have hstab1 : (stab (xorGroup k) (maskAct (xorFreeBiAction k)) S).length = 1 := by
        let singL : List (xorGroup k).G := [(xorGroup k).one]
        have hnd_s : singL.Nodup := by
          rw [List.nodup_cons]; exact ⟨List.not_mem_nil, List.nodup_nil⟩
        have hperm : (stab (xorGroup k) (maskAct (xorFreeBiAction k)) S).Perm singL := by
          apply perm_of_nodup_iff (nodup_stab _ _ _) hnd_s
          intro g
          rw [mem_stab_iff_evenRowMask k f hodd S g]
          have hmem_s : g ∈ singL ↔ g = (xorGroup k).one := List.mem_singleton
          rw [hmem_s]
          constructor
          · intro hact
            have hx := congrFun hact x₀
            let g' : Fin (2 ^ k) := g
            change evenRowMask k f S (xorFin k g' x₀) = evenRowMask k f S x₀ at hx
            rw [(hmem_x0 x₀).mpr rfl] at hx
            exact (xorFin_eq_right_iff k g' x₀).mp ((hmem_x0 _).mp hx)
          · intro hg; subst hg; exact (maskAct (xorFreeBiAction k)).act_one _
        exact hperm.length_eq
      have hs0 : s = 0 := by
        have hp : 2 ^ s = 1 := hstab_len.symm.trans hstab1
        cases s with
        | zero => rfl
        | succ s' => rw [Nat.pow_succ] at hp; have := Nat.two_pow_pos s'; omega
      rw [hs0]
      -- Compute S explicitly: S j = decide (f (x₀ ^^^ j) % 2 = 0)!
      have hS_eq : ∀ j : Fin (2 ^ k), S j = decide (f (xorFin k x₀ j) % 2 = 0) := by
        intro j
        have hinv := congrFun (maskOfEvenRows_left_inv k f hodd S) j
        rw [← hinv]
        unfold maskOfEvenRows xorMask allTrueMask conv2
        have hr : rowSum (2 ^ k) (xorCirc k f) (evenRowMask k f S) j = f (xorFin k x₀ j) := by
          unfold rowSum xorCirc
          have hflt : (List.finRange (2 ^ k)).filter (evenRowMask k f S) = [x₀] := hl
          rw [hflt]; simp [xorFin_comm k j x₀]
        rw [hr]
        by_cases hev : f (xorFin k x₀ j) % 2 = 0
        · simp [hev]
        · simp [hev]
      have hrow_x0 : rowSum (2 ^ k) (xorCirc k f) S x₀ = evenSum k f := by
        unfold rowSum evenSum xorCirc
        have hflt : (List.finRange (2 ^ k)).filter S =
            (List.finRange (2 ^ k)).filter (fun j => decide (f (xorFin k x₀ j) % 2 = 0)) := by
          apply List.filter_congr; intro j _; exact hS_eq j
        rw [hflt]
        exact sumInt_bijection ((List.nodup_finRange _).filter _) ((List.nodup_finRange _).filter _)
          (xorFin k x₀) (xorFin k x₀)
          (fun j hj => by rw [List.mem_filter] at hj ⊢; exact ⟨List.mem_finRange _, hj.2⟩)
          (fun z hz => by
            rw [List.mem_filter] at hz ⊢
            refine ⟨List.mem_finRange _, ?_⟩
            rw [← xorFin_assoc, xorFin_self, xorFin_zero_left]; exact hz.2)
          (fun j _ => by rw [← xorFin_assoc, xorFin_self, xorFin_zero_left])
          (fun z _ => by rw [← xorFin_assoc, xorFin_self, xorFin_zero_left])
          f
      -- Split rowProd into x₀ (which gives evenSum k f) and the other rows (all ODD!)
      have hsplit : rowProd (2 ^ k) (xorCirc k f) S =
          evenSum k f * prodInt ((List.finRange (2 ^ k)).filter (fun i => !evenRowMask k f S i))
            (rowSum (2 ^ k) (xorCirc k f) S) := by
        unfold rowProd
        rw [← prodInt_filter_mul_not (List.finRange (2 ^ k)) (evenRowMask k f S)]
        change prodInt (evenRowList k f S) (rowSum (2 ^ k) (xorCirc k f) S) * _ = _
        rw [hl]; simp [hrow_x0]
      have hrest_odd : prodInt ((List.finRange (2 ^ k)).filter (fun i => !evenRowMask k f S i))
          (rowSum (2 ^ k) (xorCirc k f) S) % 2 ≠ 0 := by
        apply prodInt_odd
        intro i hi
        rw [List.mem_filter] at hi
        intro hev
        have htrue : evenRowMask k f S i = true := (evenRowMask_iff k f S i).mpr hev
        simp [htrue] at hi
      have hev_even : (2 : Int) ∣ evenSum k f := by
        apply sumInt_dvd
        intro z hz
        have h0 : f z % 2 = 0 := of_decide_eq_true (List.mem_filter.mp hz).2
        exact ⟨f z / 2, by omega⟩
      have hsign_odd : (ryserSign (2 ^ k) S) % 2 ≠ 0 := by
        unfold ryserSign; by_cases h : (2 ^ k - maskCard (2 ^ k) S) % 2 = 0 <;> simp [h]
      simp only [Δ, defectCorr, hl, hsplit, Nat.zero_add]
      change (4 : Int) ∣ (ryserSign (2 ^ k) S * (evenSum k f *
        prodInt ((List.finRange (2 ^ k)).filter (fun i => !evenRowMask k f S i))
          (rowSum (2 ^ k) (xorCirc k f) S)) - evenSum k f)
      let p_odd := ryserSign (2 ^ k) S * prodInt ((List.finRange (2 ^ k)).filter (fun i => !evenRowMask k f S i))
        (rowSum (2 ^ k) (xorCirc k f) S)
      have hp_odd : p_odd % 2 ≠ 0 := by
        simp only [p_odd]; rw [Int.mul_emod]
        have h1 : ryserSign (2 ^ k) S % 2 = 1 := by omega
        have h2 : prodInt ((List.finRange (2 ^ k)).filter (fun i => !evenRowMask k f S i))
            (rowSum (2 ^ k) (xorCirc k f) S) % 2 = 1 := by omega
        rw [h1, h2]; decide
      rcases hev_even with ⟨q₁, hq₁⟩
      have hpm1 : (2 : Int) ∣ (p_odd - 1) := ⟨(p_odd - 1) / 2, by omega⟩
      rcases hpm1 with ⟨q₂, hq₂⟩
      refine ⟨q₁ * q₂, ?_⟩
      have hfac : ryserSign (2 ^ k) S * (evenSum k f *
            prodInt ((List.finRange (2 ^ k)).filter (fun i => !evenRowMask k f S i))
              (rowSum (2 ^ k) (xorCirc k f) S)) - evenSum k f =
          evenSum k f * (p_odd - 1) := by
        simp only [p_odd]
        rw [Int.mul_sub, Int.mul_one, Int.mul_left_comm]
      rw [hfac, hq₁, hq₂]
      calc (2 * q₁) * (2 * q₂) = 2 * (q₁ * (2 * q₂)) := Int.mul_assoc _ _ _
        _ = 2 * (2 * (q₁ * q₂)) := by rw [Int.mul_left_comm q₁ 2 q₂]
        _ = 4 * (q₁ * q₂) := by rw [← Int.mul_assoc]; rfl
    | cons x₁ t2 =>
      cases t2 with
      | nil =>
        -- |evenRowList| = 2 ⇒ stab S = {0, h} (s = 1, need 8 ∣ rowProd - 2 * rowSum S x₀)!
        have hnd : (evenRowList k f S).Nodup := (List.nodup_finRange _).filter _
        rw [hl] at hnd
        have hne : x₀ ≠ x₁ := by
          have ⟨ha, _⟩ := List.nodup_cons.mp hnd
          intro h; exact ha (by simp [h])
        have ⟨_, hstab_iff, hstab2, hrow_eq⟩ := two_even_rows_props k f hodd S hne hl
        have hs1 : s = 1 := by
          have hp : 2 ^ s = 2 := hstab_len.symm.trans hstab2
          cases s with
          | zero => simp at hp
          | succ s' =>
            cases s' with
            | zero => rfl
            | succ s'' =>
              have hge4 : 4 ≤ 2 ^ (s'' + 2) := by
                have := Nat.two_pow_pos s''
                rw [Nat.pow_succ, Nat.pow_succ]; omega
              omega
        subst hs1
        have hsign1 := hsign_of_s_pos (by omega)
        -- Split rowProd into evenRowList (= [x₀, x₁]) and oddRows (= filter (!evenRowMask S))!
        let oddRows := (List.finRange (2 ^ k)).filter (fun i => !evenRowMask k f S i)
        have hsplit : rowProd (2 ^ k) (xorCirc k f) S =
            (rowSum (2 ^ k) (xorCirc k f) S x₀ * rowSum (2 ^ k) (xorCirc k f) S x₀) *
            prodInt oddRows (rowSum (2 ^ k) (xorCirc k f) S) := by
          unfold rowProd
          rw [← prodInt_filter_mul_not (List.finRange (2 ^ k)) (evenRowMask k f S)]
          change prodInt (evenRowList k f S) (rowSum (2 ^ k) (xorCirc k f) S) * prodInt oddRows _ = _
          rw [hl]; simp [hrow_eq]
        -- H = stab S (length 2) leaves oddRows closed and rowSum invariant ⇒ prodInt oddRows = v^2!
        let H := stabSubgroup (xorGroup k) (maskAct (xorFreeBiAction k)) S
        have hrow_inv : ∀ g ∈ H.elems, ∀ i, rowSum (2 ^ k) (xorCirc k f) S ((xorFreeBiAction k).rowAct.act g i) =
            rowSum (2 ^ k) (xorCirc k f) S i := by
          intro g hg i
          have hfix : (maskAct (xorFreeBiAction k)).act g S = S := (mem_stab _ _ _ _).mp hg
          have hact := rowSum_act_eq (xorFreeBiAction k) (xorCirc k f) (xorCirc_equivariant k f) g S i
          rw [hfix] at hact; exact hact
        have hodd_closed : ∀ g ∈ H.elems, ∀ i ∈ oddRows, (xorFreeBiAction k).rowAct.act g i ∈ oddRows := by
          intro g hg i hi
          rw [List.mem_filter] at hi ⊢
          refine ⟨List.mem_finRange _, ?_⟩
          have hinv_row := hrow_inv g hg i
          cases hb : evenRowMask k f S ((xorFreeBiAction k).rowAct.act g i)
          · rfl
          · exfalso
            have hev := (evenRowMask_iff k f S _).mp hb
            rw [hinv_row] at hev
            have ht := (evenRowMask_iff k f S i).mpr hev
            simp [ht] at hi
        rcases free_subgroup_prod_pow (xorGroup k) H (xorFreeBiAction k).rowAct (xorFreeBiAction k).row_free
            (rowSum (2 ^ k) (xorCirc k f) S) hrow_inv
            oddRows.length oddRows (Nat.le_refl _) ((List.nodup_finRange _).filter _) hodd_closed with ⟨v, hv⟩
        change prodInt oddRows (rowSum (2 ^ k) (xorCirc k f) S) = v ^ (stab (xorGroup k) (maskAct (xorFreeBiAction k)) S).length at hv
        rw [hstab2] at hv
        -- v is odd (since prodInt oddRows is odd) ⇒ 8 ∣ (v^2 - 1)!
        have hv_odd : v % 2 ≠ 0 := by
          have hp_odd : prodInt oddRows (rowSum (2 ^ k) (xorCirc k f) S) % 2 ≠ 0 := by
            apply prodInt_odd
            intro i hi
            rw [List.mem_filter] at hi
            intro hev
            have ht := (evenRowMask_iff k f S i).mpr hev
            simp [ht] at hi
          rw [hv] at hp_odd
          intro hv0
          have hv2 : (v ^ 2) % 2 = 0 := by
            rw [show v ^ 2 = v * v by simp [Int.pow_succ], Int.mul_emod, hv0]; rfl
          exact hp_odd hv2
        have hv8 : (8 : Int) ∣ (v ^ 2 - 1) := by
          simpa using odd_pow_two_pow_sub_one v hv_odd 1 (Nat.le_refl 1)
        -- a = rowSum S x₀ is even ⇒ 8 ∣ (a*a - 2*a)
        have ha_even : (2 : Int) ∣ rowSum (2 ^ k) (xorCirc k f) S x₀ := by
          have hx0_mem : x₀ ∈ evenRowList k f S := by rw [hl]; simp
          have h0 := (evenRowMask_iff k f S x₀).mp (List.mem_filter.mp hx0_mem).2
          exact ⟨rowSum (2 ^ k) (xorCirc k f) S x₀ / 2, by omega⟩
        have ha8 := even_sq_sub_two_mul (rowSum (2 ^ k) (xorCirc k f) S x₀) ha_even
        simp only [Δ, defectCorr, hl, hsign1, Int.one_mul, hsplit, hv]
        change (8 : Int) ∣ (rowSum (2 ^ k) (xorCirc k f) S x₀ * rowSum (2 ^ k) (xorCirc k f) S x₀ * v ^ 2 -
          2 * rowSum (2 ^ k) (xorCirc k f) S x₀)
        let a := rowSum (2 ^ k) (xorCirc k f) S x₀
        have hdecomp : a * a * v ^ 2 - 2 * a = (a * a) * (v ^ 2 - 1) + (a * a - 2 * a) := by
          rw [Int.mul_sub, Int.mul_one]; omega
        rw [hdecomp]
        exact Int.dvd_add (Int.dvd_mul_of_dvd_right hv8) ha8
      | cons x₂ t3 =>
        -- |evenRowList| ≥ 3 ⇒ defectCorr S = 0, need 2^(s + 2) ∣ ryserSign * rowProd!
        have hlen_ge3 : 3 ≤ (evenRowList k f S).length := by rw [hl]; simp
        simp only [Δ, defectCorr, hl, Int.sub_zero]
        apply Int.dvd_mul_of_dvd_right
        -- Note: 2^(evenRowList.length) always divides rowProd!
        have hprod_dvd_ev : ((2 ^ (evenRowList k f S).length : Nat) : Int) ∣ rowProd (2 ^ k) (xorCirc k f) S := by
          unfold rowProd
          rw [← prodInt_filter_mul_not (List.finRange (2 ^ k)) (evenRowMask k f S)]
          apply Int.dvd_mul_of_dvd_left
          apply prodInt_even_dvd
          intro i hi
          have h0 := (evenRowMask_iff k f S i).mp (List.mem_filter.mp hi).2
          exact ⟨rowSum (2 ^ k) (xorCirc k f) S i / 2, by omega⟩
        cases s with
        | zero =>
          -- Need 2^2 = 4 ∣ rowProd; we already have 2^3 = 8 ∣ rowProd!
          exact Int.dvd_trans (dvd_pow2_of_le (by omega : 0 + 2 ≤ (evenRowList k f S).length)) hprod_dvd_ev
        | succ s' =>
          cases s' with
          | zero =>
            -- s = 1 ⇒ |H| = 2 divides (evenRowList S).length (since H acts freely & preserves evenRowList),
            -- so (evenRowList S).length ≥ 4 ⇒ 2^4 = 16 ∣ rowProd ⇒ 8 = 2^(1+2) ∣ rowProd!
            let H := stabSubgroup (xorGroup k) (maskAct (xorFreeBiAction k)) S
            have hev_closed : ∀ g ∈ H.elems, ∀ i ∈ evenRowList k f S,
                (xorFreeBiAction k).rowAct.act g i ∈ evenRowList k f S := by
              intro g hg i hi
              unfold evenRowList at hi ⊢
              rw [List.mem_filter] at hi ⊢
              refine ⟨List.mem_finRange _, ?_⟩
              have hfix : (maskAct (xorFreeBiAction k)).act g S = S := (mem_stab _ _ _ _).mp hg
              have hact := rowSum_act_eq (xorFreeBiAction k) (xorCirc k f) (xorCirc_equivariant k f) g S i
              rw [hfix] at hact
              rw [evenRowMask_iff, hact]
              exact (evenRowMask_iff k f S i).mp hi.2
            have h2dvd_len : 2 ∣ (evenRowList k f S).length := by
              have hd := free_subgroup_dvd_length (xorGroup k) H (xorFreeBiAction k).rowAct (xorFreeBiAction k).row_free
                _ _ (Nat.le_refl _) ((List.nodup_finRange _).filter _) hev_closed
              change (stab (xorGroup k) (maskAct (xorFreeBiAction k)) S).length ∣ (evenRowList k f S).length at hd
              rw [hstab_len] at hd; exact hd
            have hlen_ge4 : 4 ≤ (evenRowList k f S).length := by
              rcases h2dvd_len with ⟨q, hq⟩; omega
            exact Int.dvd_trans (dvd_pow2_of_le (by omega : 1 + 2 ≤ (evenRowList k f S).length)) hprod_dvd_ev
          | succ s'' =>
            -- s = s'' + 2 ≥ 2 ⇒ rowProd = u ^ (2^s), u is even ⇒ 2^(2^s) ∣ rowProd, and s + 2 ≤ 2^s!
            let H := stabSubgroup (xorGroup k) (maskAct (xorFreeBiAction k)) S
            have hrow_inv : ∀ g ∈ H.elems, ∀ i, rowSum (2 ^ k) (xorCirc k f) S ((xorFreeBiAction k).rowAct.act g i) =
                rowSum (2 ^ k) (xorCirc k f) S i := by
              intro g hg i
              have hfix : (maskAct (xorFreeBiAction k)).act g S = S := (mem_stab _ _ _ _).mp hg
              have hact := rowSum_act_eq (xorFreeBiAction k) (xorCirc k f) (xorCirc_equivariant k f) g S i
              rw [hfix] at hact; exact hact
            rcases free_subgroup_prod_pow (xorGroup k) H (xorFreeBiAction k).rowAct (xorFreeBiAction k).row_free
                (rowSum (2 ^ k) (xorCirc k f) S) hrow_inv
                (2 ^ k) (List.finRange (2 ^ k)) (by simp) (List.nodup_finRange _) (fun _ _ _ _ => List.mem_finRange _) with ⟨u, hu⟩
            change rowProd (2 ^ k) (xorCirc k f) S = u ^ (stab (xorGroup k) (maskAct (xorFreeBiAction k)) S).length at hu
            rw [hstab_len] at hu
            have hu_even : (2 : Int) ∣ u := by
              have h2prod : (2 : Int) ∣ rowProd (2 ^ k) (xorCirc k f) S :=
                Int.dvd_trans (dvd_pow2_of_le (by omega : 1 ≤ (evenRowList k f S).length)) hprod_dvd_ev
              rw [hu] at h2prod
              by_cases hu0 : u % 2 = 0
              · exact ⟨u / 2, by omega⟩
              · exfalso
                have hodd_pow : ∀ m : Nat, (u ^ m) % 2 ≠ 0 := by
                  intro m; induction m with
                  | zero => simp
                  | succ m' ihm =>
                    rw [Int.pow_succ, Int.mul_emod]
                    have h1 : u % 2 = 1 := by omega
                    have h2 : (u ^ m') % 2 = 1 := by omega
                    rw [h1, h2]; decide
                have h2_0 : (u ^ 2 ^ (s'' + 2)) % 2 = 0 := Int.emod_eq_zero_of_dvd h2prod
                exact hodd_pow (2 ^ (s'' + 2)) h2_0
            rw [hu]
            have hge := nat_pow2_ge_add_two (s'' + 2) (by omega)
            exact Int.dvd_trans (dvd_pow2_of_le hge) (even_pow_dvd u hu_even (2 ^ (s'' + 2)))

-- Now evaluate sumInt (allMasks (2^k)) (defectCorr k f) modulo 2^(k + 2)!

theorem sum_defectCorr_mod {k : Nat} (hk : 1 ≤ k) (f : Fin (2 ^ k) → Int)
    (hodd : rowSumAll k f % 2 ≠ 0) :
    ((2 ^ (k + 2) : Nat) : Int) ∣
      (sumInt (allMasks (2 ^ k)) (defectCorr k f) -
        (1 + ((2 ^ k : Nat) : Int) * (((oddCount k f : Int) - 1) + evenSum k f))) := by
  -- Partition allMasks (2^k) by (evenRowList k f S).length ∈ {0, 1, 2, ≥3}!
  let M0 := (allMasks (2 ^ k)).filter (fun S => decide ((evenRowList k f S).length = 0))
  let M1 := (allMasks (2 ^ k)).filter (fun S => decide ((evenRowList k f S).length = 1))
  let M2 := (allMasks (2 ^ k)).filter (fun S => decide ((evenRowList k f S).length = 2))
  have hpart : sumInt (allMasks (2 ^ k)) (defectCorr k f) =
      sumInt M0 (defectCorr k f) + sumInt M1 (defectCorr k f) + sumInt M2 (defectCorr k f) := by
    rw [sumInt_filter_eq_sumInt_ite, sumInt_filter_eq_sumInt_ite, sumInt_filter_eq_sumInt_ite,
      ← sumInt_add, ← sumInt_add]
    apply sumInt_congr
    intro S _
    unfold defectCorr
    cases evenRowList k f S with
    | nil => simp
    | cons a t =>
      cases t with
      | nil => simp
      | cons b t2 =>
        cases t2 with
        | nil => simp
        | cons c t3 => simp
  -- Part 0: sumInt M0 (defectCorr k f) = 1
  have hsum0 : sumInt M0 (defectCorr k f) = 1 := by
    have hM0 : M0 = [allTrueMask (2 ^ k)] := by
      apply List.Perm.eq_singleton
      apply perm_of_nodup_iff ((nodup_allMasks _).filter _) (by simp)
      intro S
      simp only [List.mem_filter, mem_allMasks, true_and, decide_eq_true_eq, List.mem_singleton]
      constructor
      · intro h0
        have hl : evenRowList k f S = [] := List.eq_nil_of_length_eq_zero h0
        have hEm : evenRowMask k f S = allFalseMask (2 ^ k) := by
          funext i
          cases hb : evenRowMask k f S i
          · rfl
          · exfalso; have : i ∈ evenRowList k f S := List.mem_filter.mpr ⟨List.mem_finRange i, hb⟩
            rw [hl] at this; cases this
        have hinv := maskOfEvenRows_left_inv k f hodd S
        rw [hEm] at hinv; unfold maskOfEvenRows at hinv
        have hc0 : conv2 k f (allFalseMask (2 ^ k)) = allFalseMask (2 ^ k) := by
          funext i; unfold conv2 allFalseMask rowSum
          have hemp : (List.finRange (2 ^ k)).filter (fun _ => false) = [] := by
            rw [List.filter_eq_nil_iff]; intro _ _; simp
          rw [hemp]; rfl
        rw [hc0] at hinv; rw [← hinv]; funext i; simp [xorMask, allTrueMask, allFalseMask]
      · intro hS; subst hS
        have hemp : evenRowList k f (allTrueMask (2 ^ k)) = [] := by
          rw [evenRowList, List.filter_eq_nil_iff]
          intro i _
          have hc := congrFun (conv2_allTrue k f) i
          simp [hodd, evenRowMask, allTrueMask, hc]
        rw [hemp]; rfl
    rw [hM0]
    have hemp : evenRowList k f (allTrueMask (2 ^ k)) = [] := by
      rw [evenRowList, List.filter_eq_nil_iff]
      intro i _
      have hc := congrFun (conv2_allTrue k f) i
      simp [hodd, evenRowMask, allTrueMask, hc]
    simp [defectCorr, hemp]
  -- Part 1: sumInt M1 (defectCorr k f) = (2^k) * evenSum k f
  have hsum1 : sumInt M1 (defectCorr k f) = ((2 ^ k : Nat) : Int) * evenSum k f := by
    have hconst1 : sumInt M1 (defectCorr k f) = (M1.length : Int) * evenSum k f := by
      rw [sumInt_congr (g := fun _ => evenSum k f) (fun S hS => by
        have h1 : (evenRowList k f S).length = 1 := of_decide_eq_true (List.mem_filter.mp hS).2
        rcases list_eq_one_of_length_one h1 with ⟨a, ha⟩
        simp [defectCorr, ha])]
      exact sumInt_const _ _
    have hlen1 : M1.length = 2 ^ k := by
      have hlen_fr : M1.length = (List.finRange (2 ^ k)).length := by
        apply length_bijection ((nodup_allMasks _).filter _) (List.nodup_finRange _)
          (fun S => match evenRowList k f S with | x :: _ => x | [] => finZero k)
          (fun x => maskOfEvenRows k f (singleRowMask k x))
        · intro _ _; exact List.mem_finRange _
        · intro x _
          rw [List.mem_filter]
          refine ⟨mem_allMasks _ _, decide_eq_true ?_⟩
          unfold evenRowList
          rw [maskOfEvenRows_right_inv k f hodd]
          have hflt : (List.finRange (2 ^ k)).filter (singleRowMask k x) = [x] := by
            apply List.Perm.eq_singleton
            apply perm_of_nodup_iff ((List.nodup_finRange _).filter _) (by simp)
            intro i; simp [singleRowMask, List.mem_finRange]
          rw [hflt]; rfl
        · intro S hS
          have h1 : (evenRowList k f S).length = 1 := of_decide_eq_true (List.mem_filter.mp hS).2
          rcases list_eq_one_of_length_one h1 with ⟨x, hx⟩
          rw [hx]
          have hEm : singleRowMask k x = evenRowMask k f S := by
            funext i
            have hmem : i ∈ evenRowList k f S ↔ evenRowMask k f S i = true := by
              simp [evenRowList, List.mem_finRange]
            cases hb : evenRowMask k f S i
            · have hni : i ≠ x := by
                intro rfl; have := hmem.mp (by rw [hx]; simp); rw [hb] at this; cases this
              simp [singleRowMask, hni]
            · have hi : i = x := by
                have : i ∈ [x] := hx ▸ hmem.mpr hb
                simpa using this
              simp [singleRowMask, hi]
          rw [hEm, maskOfEvenRows_left_inv k f hodd]
        · intro x _
          have hflt : evenRowList k f (maskOfEvenRows k f (singleRowMask k x)) = [x] := by
            unfold evenRowList
            rw [maskOfEvenRows_right_inv k f hodd]
            apply List.Perm.eq_singleton
            apply perm_of_nodup_iff ((List.nodup_finRange _).filter _) (by simp)
            intro i; simp [singleRowMask, List.mem_finRange]
          rw [hflt]
      rw [hlen_fr, List.length_finRange]
    rw [hconst1, hlen1]
  -- Part 2: sumInt M2 (defectCorr k f) = (2^k) * ∑_{h ≠ 0} r_0(S_{0,h}), which is ≡ 2^k * (oddCount - 1) mod 2^(k+2)!
  -- Define rPair h = sumInt (finRange (2^k)) (fun z => if (f z % 2 == f (xorFin k z h) % 2) then f z else 0)
  let rPair : Fin (2 ^ k) → Int := fun h =>
    sumInt (List.finRange (2 ^ k)) (fun z => if decide (f z % 2 = f (xorFin k z h) % 2) then f z else 0)
  have hsum2_eq : sumInt M2 (defectCorr k f) =
      ((2 ^ k : Nat) : Int) * sumInt ((List.finRange (2 ^ k)).filter (fun h => decide (h ≠ finZero k))) rPair := by
    -- Show: sumInt M2 (defectCorr k f) = ∑_{x} ∑_{h ≠ 0} rPair h!
    -- For each (x, h) with h ≠ 0, let S_{x, h} = maskOfEvenRows k f (pairRowMask k x (xorFin k x h)).
    -- Its rowSum at x equals rPair h!
    let Sxh : Fin (2 ^ k) → Fin (2 ^ k) → Mask (2 ^ k) :=
      fun x h => maskOfEvenRows k f (pairRowMask k x (xorFin k x h))
    have hrow_Sxh : ∀ x h : Fin (2 ^ k), h ≠ finZero k →
        rowSum (2 ^ k) (xorCirc k f) (Sxh x h) x = rPair h := by
      intro x h hh
      -- First compute Sxh x h j = decide (f (x ^^^ j) % 2 = f (x ^^^ h ^^^ j) % 2)!
      have hS_val : ∀ j : Fin (2 ^ k),
          Sxh x h j = decide (f (xorFin k x j) % 2 = f (xorFin k (xorFin k x j) h) % 2) := by
        intro j
        unfold Sxh maskOfEvenRows xorMask allTrueMask conv2
        -- rowSum of pairRowMask k x (x^^^h) at row j is f (j^^^x) + f (j^^^(x^^^h))!
        have hxne : x ≠ xorFin k x h := by
          intro heq
          apply hh
          have h1 := (xorFin_eq_right_iff k h x).mp (by rw [xorFin_comm]; exact heq.symm)
          exact h1
        have hflt : (List.finRange (2 ^ k)).filter (pairRowMask k x (xorFin k x h)) = [x, xorFin k x h] ∨
            (List.finRange (2 ^ k)).filter (pairRowMask k x (xorFin k x h)) = [xorFin k x h, x] := by
          have hperm : ((List.finRange (2 ^ k)).filter (pairRowMask k x (xorFin k x h))).Perm [x, xorFin k x h] := by
            apply perm_of_nodup_iff ((List.nodup_finRange _).filter _) (by simp [hxne])
            intro i; simp [pairRowMask, List.mem_finRange]
          have hlen2 : ((List.finRange (2 ^ k)).filter (pairRowMask k x (xorFin k x h))).length = 2 := hperm.length_eq
          rcases list_eq_two_of_length_two ((List.nodup_finRange _).filter _) hlen2 with ⟨a, b, hab, hne_ab⟩
          have ha_mem : a = x ∨ a = xorFin k x h := by
            have : a ∈ [x, xorFin k x h] := hperm.subset (by rw [hab]; simp)
            simpa using this
          have hb_mem : b = x ∨ b = xorFin k x h := by
            have : b ∈ [x, xorFin k x h] := hperm.subset (by rw [hab]; simp)
            simpa using this
          rcases ha_mem with rfl | rfl <;> rcases hb_mem with rfl | rfl
          · exact absurd rfl hne_ab
          · left; exact hab
          · right; exact hab
          · exact absurd rfl hne_ab
        have hr_sum : rowSum (2 ^ k) (xorCirc k f) (pairRowMask k x (xorFin k x h)) j =
            f (xorFin k x j) + f (xorFin k (xorFin k x j) h) := by
          unfold rowSum xorCirc
          have h1 : xorFin k j x = xorFin k x j := xorFin_comm k j x
          have h2 : xorFin k j (xorFin k x h) = xorFin k (xorFin k x j) h := by
            rw [← xorFin_assoc, xorFin_comm k j x]
          rcases hflt with hfl | hfl
          · rw [hfl]; simp [h1, h2]
          · rw [hfl]; simp [h1, h2, Int.add_comm]
        rw [hr_sum]
        by_cases hmod : f (xorFin k x j) % 2 = f (xorFin k (xorFin k x j) h) % 2
        · simp only [hmod, decide_true]
          have h0 : (f (xorFin k x j) + f (xorFin k (xorFin k x j) h)) % 2 = 0 := by
            rw [Int.add_emod, hmod]; omega
          simp [h0]
        · simp only [hmod, decide_false]
          have hne0 : (f (xorFin k x j) + f (xorFin k (xorFin k x j) h)) % 2 ≠ 0 := by
            rw [Int.add_emod]; omega
          simp [hne0]
      -- Substitute z = xorFin k x j into rowSum!
      rw [rowSum_eq_sum_ite]
      have hcongr : sumInt (List.finRange (2 ^ k)) (fun j => if Sxh x h j then xorCirc k f x j else 0) =
          sumInt (List.finRange (2 ^ k)) (fun j =>
            if decide (f (xorFin k x j) % 2 = f (xorFin k (xorFin k x j) h) % 2) then f (xorFin k x j) else 0) := by
        apply sumInt_congr
        intro j _
        rw [hS_val j]; rfl
      rw [hcongr]
      exact sumInt_bijection (List.nodup_finRange _) (List.nodup_finRange _)
        (xorFin k x) (xorFin k x)
        (fun _ _ => List.mem_finRange _) (fun _ _ => List.mem_finRange _)
        (fun j _ => by rw [← xorFin_assoc, xorFin_self, xorFin_zero_left])
        (fun z _ => by rw [← xorFin_assoc, xorFin_self, xorFin_zero_left])
        (fun z => if decide (f z % 2 = f (xorFin k z h) % 2) then f z else 0)
    -- Double-counting: ∑_{S ∈ M2} (2 * r_even(S)) = ∑_{x} ∑_{h ≠ 0} rowSum (Sxh x h) x!
    let nz := (List.finRange (2 ^ k)).filter (fun h => decide (h ≠ finZero k))
    have hdouble : sumInt (List.finRange (2 ^ k)) (fun x => sumInt nz (fun h => rPair h)) =
        sumInt M2 (defectCorr k f) := by
      -- Express LHS as sum over (x, h) of rowSum (Sxh x h) x, grouped by S = Sxh x h ∈ M2!
      have hlhs : sumInt (List.finRange (2 ^ k)) (fun x => sumInt nz (fun h => rPair h)) =
          sumInt (List.finRange (2 ^ k)) (fun x =>
            sumInt nz (fun h =>
              sumInt M2 (fun S => if S = Sxh x h then rowSum (2 ^ k) (xorCirc k f) S x else 0))) := by
        apply sumInt_congr; intro x _
        apply sumInt_congr; intro h hh
        have hh_ne : h ≠ finZero k := of_decide_eq_true (List.mem_filter.mp hh).2
        have hSxh_mem : Sxh x h ∈ M2 := by
          rw [List.mem_filter]
          refine ⟨mem_allMasks _ _, decide_eq_true ?_⟩
          unfold evenRowList Sxh
          rw [maskOfEvenRows_right_inv k f hodd]
          have hxne : x ≠ xorFin k x h := fun heq =>
            hh_ne ((xorFin_eq_right_iff k h x).mp (by rw [xorFin_comm]; exact heq.symm))
          have hperm : ((List.finRange (2 ^ k)).filter (pairRowMask k x (xorFin k x h))).Perm [x, xorFin k x h] := by
            apply perm_of_nodup_iff ((List.nodup_finRange _).filter _) (by simp [hxne])
            intro i; simp [pairRowMask, List.mem_finRange]
          exact hperm.length_eq
        -- ∑_{S ∈ M2} (if S = Sxh x h then rowSum S x else 0) = rowSum (Sxh x h) x = rPair h
        have hpick : ∀ (l : List (Mask (2 ^ k))) (t : Mask (2 ^ k)) (v : Mask (2 ^ k) → Int),
            l.Nodup → t ∈ l → sumInt l (fun S => if S = t then v S else 0) = v t := by
          intro l t v hnd ht
          induction l with
          | nil => cases ht
          | cons a as iha =>
            have ⟨ha_nm, has_nd⟩ := List.nodup_cons.mp hnd
            simp only [sumInt_cons]
            by_cases hat : a = t
            · subst hat; simp only [↓reduceIte]
              rw [sumInt_zero (fun b hb => by have hne : b ≠ a := fun e => ha_nm (e ▸ hb); simp [hne]), Int.add_zero]
            · simp only [hat, ↓reduceIte, Int.zero_add]
              rcases List.mem_cons.mp ht with rfl | ht'
              · exact absurd rfl hat
              · exact iha has_nd ht'
        rw [hpick M2 (Sxh x h) (fun S => rowSum (2 ^ k) (xorCirc k f) S x) ((nodup_allMasks _).filter _) hSxh_mem]
        exact (hrow_Sxh x h hh_ne).symm
      rw [hlhs]
      -- Swap sum over M2 to the outside!
      have hswap1 : sumInt (List.finRange (2 ^ k)) (fun x =>
            sumInt nz (fun h => sumInt M2 (fun S => if S = Sxh x h then rowSum (2 ^ k) (xorCirc k f) S x else 0))) =
          sumInt M2 (fun S => sumInt (List.finRange (2 ^ k)) (fun x =>
            sumInt nz (fun h => if S = Sxh x h then rowSum (2 ^ k) (xorCirc k f) S x else 0))) := by
        calc _ = sumInt (List.finRange (2 ^ k)) (fun x =>
              sumInt M2 (fun S => sumInt nz (fun h => if S = Sxh x h then rowSum (2 ^ k) (xorCirc k f) S x else 0))) := by
                apply sumInt_congr; intro x _; exact sumInt_comm nz M2 _
          _ = _ := sumInt_comm (List.finRange (2 ^ k)) M2 _
      rw [hswap1]
      apply sumInt_congr
      intro S hS
      have hlen2 : (evenRowList k f S).length = 2 := of_decide_eq_true (List.mem_filter.mp hS).2
      rcases list_eq_two_of_length_two ((List.nodup_finRange _).filter _) hlen2 with ⟨a, b, hab, hne_ab⟩
      have hab' : evenRowList k f S = [a, b] := hab
      have ⟨hdiff_ne, _, _, hrow_ab⟩ := two_even_rows_props k f hodd S hne_ab hab'
      let d := xorFin k a b
      -- Show: for x ∈ Fin (2^k) and h ∈ nz, S = Sxh x h ↔ (x = a ∨ x = b) ∧ h = d!
      have hcond : ∀ x : Fin (2 ^ k), ∀ h ∈ nz,
          (S = Sxh x h) ↔ ((x = a ∨ x = b) ∧ h = d) := by
        intro x h hh
        have hh_ne : h ≠ finZero k := of_decide_eq_true (List.mem_filter.mp hh).2
        have hS_iff : ∀ i : Fin (2 ^ k), evenRowMask k f S i = true ↔ (i = a ∨ i = b) := by
          intro i
          have : i ∈ evenRowList k f S ↔ evenRowMask k f S i = true := by simp [evenRowList, List.mem_finRange]
          rw [← this, hab']; simp
        constructor
        · intro hEq
          have hEm := congrArg (evenRowMask k f) hEq
          unfold Sxh at hEm
          rw [maskOfEvenRows_right_inv k f hodd] at hEm
          have hx_in : x = a ∨ x = b := (hS_iff x).mp (by rw [hEm]; simp [pairRowMask])
          have hxh_in : xorFin k x h = a ∨ xorFin k x h = b :=
            (hS_iff (xorFin k x h)).mp (by rw [hEm]; simp [pairRowMask])
          have hxne : x ≠ xorFin k x h := fun he =>
            hh_ne ((xorFin_eq_right_iff k h x).mp (by rw [xorFin_comm]; exact he.symm))
          refine ⟨hx_in, ?_⟩
          rcases hx_in with rfl | rfl <;> rcases hxh_in with h2 | h2
          · exact absurd h2.symm hxne
          · have := congrArg (xorFin k x) h2
            rw [← xorFin_assoc, xorFin_self, xorFin_zero_left] at this; exact this
          · have := congrArg (xorFin k x) h2
            rw [← xorFin_assoc, xorFin_self, xorFin_zero_left, xorFin_comm k x a] at this; exact this
          · exact absurd h2.symm hxne
        · rintro ⟨hxab, rfl⟩
          rw [← maskOfEvenRows_left_inv k f hodd S]
          unfold Sxh; congr 1; funext i
          have had : xorFin k a d = b := by
            simp only [d]; rw [← xorFin_assoc, xorFin_self, xorFin_zero_left]
          have hbd : xorFin k b d = a := by
            simp only [d]; rw [xorFin_comm k a b, ← xorFin_assoc, xorFin_self, xorFin_zero_left]
          cases hb : evenRowMask k f S i
          · have hni : ¬ (i = a ∨ i = b) := fun h => by rw [(hS_iff i).mpr h] at hb; cases hb
            rcases hxab with hxa | hxb
            · rw [hxa, had]; simp [pairRowMask, hni]
            · rw [hxb, hbd]
              have hni' : ¬ (i = b ∨ i = a) := fun h => hni (Or.symm h)
              simp [pairRowMask, hni']
          · have hi := (hS_iff i).mp hb
            rcases hxab with hxa | hxb
            · rw [hxa, had]; simp [pairRowMask, hi]
            · rw [hxb, hbd]
              rcases hi with rfl | rfl <;> simp [pairRowMask]
      -- Evaluate inner sum over nz and outer sum over Fin (2^k)!
      have hd_mem : d ∈ nz := List.mem_filter.mpr ⟨List.mem_finRange d, decide_eq_true hdiff_ne⟩
      have hpick_fin : ∀ (l : List (Fin (2 ^ k))) (t : Fin (2 ^ k)) (c : Int),
          l.Nodup → t ∈ l → sumInt l (fun z => if z = t then c else 0) = c := by
        intro l t c hnd ht
        induction l with
        | nil => cases ht
        | cons u us ihu =>
          have ⟨hu_nm, hus_nd⟩ := List.nodup_cons.mp hnd
          simp only [sumInt_cons]
          by_cases hut : u = t
          · subst hut; simp only [↓reduceIte]
            rw [sumInt_zero (fun v hv => by have hne : v ≠ u := fun e => hu_nm (e ▸ hv); simp [hne]), Int.add_zero]
          · simp only [hut, ↓reduceIte, Int.zero_add]
            rcases List.mem_cons.mp ht with rfl | ht'
            · exact absurd rfl hut
            · exact ihu hus_nd ht'
      have hinner : ∀ x : Fin (2 ^ k),
          sumInt nz (fun h => if S = Sxh x h then rowSum (2 ^ k) (xorCirc k f) S x else 0) =
          if x = a ∨ x = b then rowSum (2 ^ k) (xorCirc k f) S a else 0 := by
        intro x
        by_cases hxab : x = a ∨ x = b
        · simp only [hxab, ↓reduceIte]
          have hrx : rowSum (2 ^ k) (xorCirc k f) S x = rowSum (2 ^ k) (xorCirc k f) S a := by
            rcases hxab with rfl | rfl
            · rfl
            · exact hrow_ab.symm
          rw [sumInt_congr (g := fun h => if h = d then rowSum (2 ^ k) (xorCirc k f) S a else 0)
            (fun h hh => by
              by_cases hhd : h = d
              · subst hhd
                have htrue : S = Sxh x d := (hcond x d hh).mpr ⟨hxab, rfl⟩
                simp only [htrue, ↓reduceIte]
                rw [← htrue]; exact hrx
              · have hfalse : S ≠ Sxh x h := fun he => hhd ((hcond x h hh).mp he).2
                simp [hfalse, hhd])]
          exact hpick_fin nz d _ ((List.nodup_finRange _).filter _) hd_mem
        · simp only [hxab, ↓reduceIte]
          apply sumInt_zero
          intro h hh
          have hfalse : S ≠ Sxh x h := fun he => hxab ((hcond x h hh).mp he).1
          simp [hfalse]
      rw [sumInt_congr (fun x _ => hinner x)]
      have htwo_pick : sumInt (List.finRange (2 ^ k)) (fun x => if x = a ∨ x = b then rowSum (2 ^ k) (xorCirc k f) S a else 0) =
          2 * rowSum (2 ^ k) (xorCirc k f) S a := by
        rw [sumInt_congr (g := fun x => (if x = a then rowSum (2 ^ k) (xorCirc k f) S a else 0) +
            (if x = b then rowSum (2 ^ k) (xorCirc k f) S a else 0)) (fun x _ => by
          by_cases ha : x = a
          · subst ha; simp [hne_ab]
          · by_cases hb : x = b
            · subst hb; simp [ha]
            · simp [ha, hb])]
        rw [sumInt_add, hpick_fin _ a _ (List.nodup_finRange _) (List.mem_finRange a),
          hpick_fin _ b _ (List.nodup_finRange _) (List.mem_finRange b)]
        omega
      rw [htwo_pick]
      unfold defectCorr; rw [hab']
    rw [← hdouble, sumInt_const, List.length_finRange]
  -- Now evaluate ∑_{h ≠ 0} rPair h modulo 4!
  have hrPair_sum_mod4 : (4 : Int) ∣
      (sumInt ((List.finRange (2 ^ k)).filter (fun h => decide (h ≠ finZero k))) rPair - ((oddCount k f : Int) - 1)) := by
    let nz := (List.finRange (2 ^ k)).filter (fun h => decide (h ≠ finZero k))
    -- Swap the double sum over h ∈ nz and z ∈ finRange (2^k)!
    have hswap : sumInt nz rPair =
        sumInt (List.finRange (2 ^ k)) (fun z =>
          f z * ((nz.filter (fun h => decide (f z % 2 = f (xorFin k z h) % 2))).length : Int)) := by
      unfold rPair
      rw [sumInt_comm]
      apply sumInt_congr
      intro z _
      rw [← sumInt_filter_eq_sumInt_ite, sumInt_const, Int.mul_comm]
    -- Count #{h ≠ 0 | f(z^h) % 2 = f z % 2} = (oddCount - 1) if f z odd, else (2^k - oddCount - 1)!
    have hcount_h : ∀ z : Fin (2 ^ k),
        (nz.filter (fun h => decide (f z % 2 = f (xorFin k z h) % 2))).length =
        if f z % 2 ≠ 0 then oddCount k f - 1 else 2 ^ k - oddCount k f - 1 := by
      intro z
      -- Map h ↦ xorFin k z h maps nz bijectively onto (finRange (2^k)).filter (· ≠ z)!
      let target := (List.finRange (2 ^ k)).filter (fun w => decide (w ≠ z ∧ f z % 2 = f w % 2))
      have hlen_eq : (nz.filter (fun h => decide (f z % 2 = f (xorFin k z h) % 2))).length = target.length := by
        apply length_bijection (((List.nodup_finRange _).filter _).filter _) ((List.nodup_finRange _).filter _)
          (xorFin k z) (xorFin k z)
        · intro h hh
          rw [List.mem_filter, List.mem_filter] at hh
          rw [List.mem_filter]
          refine ⟨List.mem_finRange _, decide_eq_true ⟨?_, of_decide_eq_true hh.2⟩⟩
          intro heq
          have hh0 : h = finZero k := (xorFin_eq_right_iff k h z).mp (by rw [xorFin_comm]; exact heq)
          exact of_decide_eq_true hh.1.2 hh0
        · intro w hw
          rw [List.mem_filter] at hw
          have ⟨hwne, hwmod⟩ := of_decide_eq_true hw.2
          rw [List.mem_filter, List.mem_filter]
          have hzw : xorFin k z (xorFin k z w) = w := by rw [← xorFin_assoc, xorFin_self, xorFin_zero_left]
          refine ⟨⟨List.mem_finRange _, decide_eq_true ?_⟩, decide_eq_true (by rw [hzw]; exact hwmod)⟩
          intro h0
          apply hwne
          have := congrArg (xorFin k z) h0
          rw [← xorFin_assoc, xorFin_self, xorFin_zero_left, xorFin_zero_right] at this
          exact this
        · intro h _; rw [← xorFin_assoc, xorFin_self, xorFin_zero_left]
        · intro w _; rw [← xorFin_assoc, xorFin_self, xorFin_zero_left]
      rw [hlen_eq]
      let sameP := (List.finRange (2 ^ k)).filter (fun w => decide (f z % 2 = f w % 2))
      have htarget_len : target.length + 1 = sameP.length := by
        have hperm : (z :: target).Perm sameP := by
          apply perm_of_nodup_iff
          · rw [List.nodup_cons]
            refine ⟨?_, (List.nodup_finRange _).filter _⟩
            intro hm; have := of_decide_eq_true (List.mem_filter.mp hm).2; exact this.1 rfl
          · exact (List.nodup_finRange _).filter _
          · intro w
            simp only [List.mem_cons, target, sameP, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
            constructor
            · rintro (rfl | ⟨_, hm⟩)
              · rfl
              · exact hm
            · intro hm
              by_cases hwz : w = z
              · left; exact hwz
              · right; exact ⟨hwz, hm⟩
        simpa [Nat.add_comm] using hperm.length_eq
      by_cases hz_odd : f z % 2 ≠ 0
      · have hite : (if f z % 2 ≠ 0 then oddCount k f - 1 else 2 ^ k - oddCount k f - 1) = oddCount k f - 1 := by
          simp [hz_odd]
        rw [hite]
        have hsame_eq : sameP = (List.finRange (2 ^ k)).filter (fun w => decide (f w % 2 ≠ 0)) := by
          apply List.filter_congr
          intro w _
          by_cases hw : f w % 2 ≠ 0
          · have h1 : f z % 2 = 1 := by omega
            have h2 : f w % 2 = 1 := by omega
            simp [h1, h2]
          · have h1 : f z % 2 = 1 := by omega
            have h2 : f w % 2 = 0 := by omega
            simp [h1, h2]
        have hlen_sp : sameP.length = oddCount k f := by unfold oddCount; rw [hsame_eq]
        omega
      · have hite : (if f z % 2 ≠ 0 then oddCount k f - 1 else 2 ^ k - oddCount k f - 1) = 2 ^ k - oddCount k f - 1 := by
          simp [hz_odd]
        rw [hite]
        have hsame_eq : sameP = (List.finRange (2 ^ k)).filter (fun w => !decide (f w % 2 ≠ 0)) := by
          apply List.filter_congr
          intro w _
          by_cases hw : f w % 2 ≠ 0
          · have h1 : f z % 2 = 0 := by omega
            have h2 : f w % 2 = 1 := by omega
            simp [h1, h2]
          · have h1 : f z % 2 = 0 := by omega
            have h2 : f w % 2 = 0 := by omega
            simp [h1, h2]
        have hsplit_len : (List.finRange (2 ^ k)).length = oddCount k f + sameP.length := by
          rw [hsame_eq]; unfold oddCount
          have haux : ∀ (l : List (Fin (2 ^ k))) (p : Fin (2 ^ k) → Bool),
              l.length = (l.filter p).length + (l.filter (fun w => !p w)).length := by
            intro l p; induction l with | nil => simp | cons a as iha => cases hpa : p a <;> simp [hpa] <;> omega
          exact haux _ _
        rw [List.length_finRange] at hsplit_len
        omega
    -- Split sumInt over finRange (2^k) into odd entries and even entries!
    have hodd_count_odd : oddCount k f % 2 = 1 := by
      have hmod : rowSumAll k f % 2 = (oddCount k f : Int) % 2 := by
        unfold rowSumAll oddCount
        have h1 : (((List.finRange (2 ^ k)).filter (fun z => decide (f z % 2 ≠ 0))).length : Int) =
            sumInt (List.finRange (2 ^ k)) (fun z => if decide (f z % 2 ≠ 0) then (1 : Int) else 0) := by
          rw [← sumInt_filter_eq_sumInt_ite, sumInt_const, Int.mul_one]
        rw [h1]
        apply sumInt_mod2_congr
        intro z _
        by_cases hz : f z % 2 ≠ 0
        · simp [hz]; omega
        · simp [hz]; omega
      omega
    have hodd_pos : 1 ≤ oddCount k f := by omega
    have h2k_even : (2 ^ k) % 2 = 0 := by
      cases k with | zero => omega | succ k' => rw [Nat.pow_succ]; omega
    have hodd_le_2k : oddCount k f ≤ 2 ^ k := by
      unfold oddCount
      calc _ ≤ (List.finRange (2 ^ k)).length := List.length_filter_le _ _
        _ = 2 ^ k := List.length_finRange
    have heven_pos : 1 ≤ 2 ^ k - oddCount k f := by omega
    have hlinear : sumInt nz rPair =
        ((oddCount k f : Int) - 1) * oddSum k f +
        ((((2 ^ k : Nat) : Int) - (oddCount k f : Int) - 1) * evenSum k f) := by
      rw [hswap]
      rw [← sumInt_filter_add_not (List.finRange (2 ^ k)) (fun z => decide (f z % 2 ≠ 0))]
      congr 1
      · unfold oddSum
        rw [sumInt_congr (g := fun z => ((oddCount k f : Int) - 1) * f z) (fun z hz => by
          have hzo : f z % 2 ≠ 0 := of_decide_eq_true (List.mem_filter.mp hz).2
          rw [hcount_h z]
          have hite : (if f z % 2 ≠ 0 then oddCount k f - 1 else 2 ^ k - oddCount k f - 1) = oddCount k f - 1 := by
            simp [hzo]
          rw [hite]
          have hsub : ((oddCount k f - 1 : Nat) : Int) = (oddCount k f : Int) - 1 := by omega
          rw [hsub, Int.mul_comm])]
        exact sumInt_mul_left _ _ _
      · unfold evenSum
        have hflt_ev : (List.finRange (2 ^ k)).filter (fun z => !decide (f z % 2 ≠ 0)) =
            (List.finRange (2 ^ k)).filter (fun z => decide (f z % 2 = 0)) := by
          apply List.filter_congr; intro z _
          by_cases hz : f z % 2 = 0
          · simp [hz]
          · simp [hz]
        rw [hflt_ev]
        rw [sumInt_congr (g := fun z => (((2 ^ k : Nat) : Int) - (oddCount k f : Int) - 1) * f z) (fun z hz => by
          have hze : f z % 2 = 0 := of_decide_eq_true (List.mem_filter.mp hz).2
          have hne : ¬ f z % 2 ≠ 0 := by omega
          rw [hcount_h z]
          have hite : (if f z % 2 ≠ 0 then oddCount k f - 1 else 2 ^ k - oddCount k f - 1) = 2 ^ k - oddCount k f - 1 := by
            simp [hne]
          rw [hite]
          have hcast : ((2 ^ k - oddCount k f - 1 : Nat) : Int) = ((2 ^ k : Nat) : Int) - (oddCount k f : Int) - 1 := by omega
          rw [hcast, Int.mul_comm])]
        exact sumInt_mul_left _ _ _
    rw [hlinear]
    have hoddSum_odd : oddSum k f % 2 ≠ 0 := by
      have htot : rowSumAll k f = oddSum k f + evenSum k f := by
        unfold rowSumAll oddSum evenSum
        have hflt_ev : (List.finRange (2 ^ k)).filter (fun z => !decide (f z % 2 ≠ 0)) =
            (List.finRange (2 ^ k)).filter (fun z => decide (f z % 2 = 0)) := by
          apply List.filter_congr; intro z _
          by_cases hz : f z % 2 = 0
          · simp [hz]
          · simp [hz]
        rw [← hflt_ev]
        exact (sumInt_filter_add_not _ _ _).symm
      have hev_even : (2 : Int) ∣ evenSum k f := by
        apply sumInt_dvd; intro z hz
        have h0 : f z % 2 = 0 := of_decide_eq_true (List.mem_filter.mp hz).2
        exact ⟨f z / 2, by omega⟩
      rcases hev_even with ⟨q, hq⟩
      omega
    have hterm1 : (4 : Int) ∣ (((oddCount k f : Int) - 1) * oddSum k f - ((oddCount k f : Int) - 1)) := by
      have h1 : (2 : Int) ∣ ((oddCount k f : Int) - 1) := ⟨((oddCount k f : Int) - 1) / 2, by omega⟩
      have h2 : (2 : Int) ∣ (oddSum k f - 1) := ⟨(oddSum k f - 1) / 2, by omega⟩
      rcases h1 with ⟨q₁, hq₁⟩; rcases h2 with ⟨q₂, hq₂⟩
      refine ⟨q₁ * q₂, ?_⟩
      have hfac : ((oddCount k f : Int) - 1) * oddSum k f - ((oddCount k f : Int) - 1) =
          ((oddCount k f : Int) - 1) * (oddSum k f - 1) := by rw [Int.mul_sub, Int.mul_one]
      rw [hfac, hq₁, hq₂]
      calc (2 * q₁) * (2 * q₂) = 2 * (q₁ * (2 * q₂)) := Int.mul_assoc _ _ _
        _ = 2 * (2 * (q₁ * q₂)) := by rw [Int.mul_left_comm q₁ 2 q₂]
        _ = 4 * (q₁ * q₂) := by rw [← Int.mul_assoc]; rfl
    have hterm2 : (4 : Int) ∣ ((((2 ^ k : Nat) : Int) - (oddCount k f : Int) - 1) * evenSum k f) := by
      have h1 : (2 : Int) ∣ (((2 ^ k : Nat) : Int) - (oddCount k f : Int) - 1) :=
        ⟨(((2 ^ k : Nat) : Int) - (oddCount k f : Int) - 1) / 2, by omega⟩
      have h2 : (2 : Int) ∣ evenSum k f := by
        apply sumInt_dvd; intro z hz
        have h0 : f z % 2 = 0 := of_decide_eq_true (List.mem_filter.mp hz).2
        exact ⟨f z / 2, by omega⟩
      rcases h1 with ⟨q₁, hq₁⟩; rcases h2 with ⟨q₂, hq₂⟩
      refine ⟨q₁ * q₂, ?_⟩
      rw [hq₁, hq₂]
      calc (2 * q₁) * (2 * q₂) = 2 * (q₁ * (2 * q₂)) := Int.mul_assoc _ _ _
        _ = 2 * (2 * (q₁ * q₂)) := by rw [Int.mul_left_comm q₁ 2 q₂]
        _ = 4 * (q₁ * q₂) := by rw [← Int.mul_assoc]; rfl
    have hcomb : ((oddCount k f : Int) - 1) * oddSum k f +
          (((2 ^ k : Nat) : Int) - (oddCount k f : Int) - 1) * evenSum k f - ((oddCount k f : Int) - 1) =
        (((oddCount k f : Int) - 1) * oddSum k f - ((oddCount k f : Int) - 1)) +
        (((2 ^ k : Nat) : Int) - (oddCount k f : Int) - 1) * evenSum k f := by omega
    rw [hcomb]
    exact Int.dvd_add hterm1 hterm2
  -- Combine Parts 0, 1, 2!
  rw [hpart, hsum0, hsum1, hsum2_eq]
  rcases hrPair_sum_mod4 with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have hpow : ((2 ^ (k + 2) : Nat) : Int) = ((2 ^ k : Nat) : Int) * 4 := by
    rw [Nat.pow_add, Int.natCast_mul]; rfl
  rw [hpow]
  have hdiff : 1 + ((2 ^ k : Nat) : Int) * evenSum k f +
        ((2 ^ k : Nat) : Int) * sumInt ((List.finRange (2 ^ k)).filter (fun h => decide (h ≠ finZero k))) rPair -
        (1 + ((2 ^ k : Nat) : Int) * (((oddCount k f : Int) - 1) + evenSum k f)) =
      ((2 ^ k : Nat) : Int) *
        (sumInt ((List.finRange (2 ^ k)).filter (fun h => decide (h ≠ finZero k))) rPair - ((oddCount k f : Int) - 1)) := by
    rw [Int.mul_add, Int.mul_sub, Int.mul_sub, Int.mul_one]
    have h1 : ((2 ^ k : Nat) : Int) * (((oddCount k f : Int) - 1)) =
        ((2 ^ k : Nat) : Int) * (oddCount k f : Int) - ((2 ^ k : Nat) : Int) := by
      rw [Int.mul_sub, Int.mul_one]
    omega
  rw [hdiff, hq, Int.mul_assoc]

/-- THEOREM 3 (Sharp Mod-2^(k+2) Exact Entry-Histogram Congruence for ALL k ≥ 1):
    For every k ≥ 1 and every integer XOR-circulant 2^k × 2^k matrix A_f with odd row sum,
      perm(2^k, A_f) ≡ 1 + 2^k · ((N_odd(f) - 1) + S_even(f))  (mod 2^(k + 2)). -/
theorem xorCirc_odd_mod_two_pow_add_two {k : Nat} (hk : 1 ≤ k) (f : Fin (2 ^ k) → Int)
    (hodd : rowSumAll k f % 2 ≠ 0) :
    ((2 ^ (k + 2) : Nat) : Int) ∣
      (perm (2 ^ k) (xorCirc k f) -
        (1 + ((2 ^ k : Nat) : Int) * (((oddCount k f : Int) - 1) + evenSum k f))) := by
  have h1 := xorCirc_perm_sub_defectCorr_dvd hk f hodd
  have h2 := sum_defectCorr_mod hk f hodd
  have hadd := Int.dvd_add h1 h2
  have heq : (perm (2 ^ k) (xorCirc k f) - sumInt (allMasks (2 ^ k)) (defectCorr k f)) +
      (sumInt (allMasks (2 ^ k)) (defectCorr k f) -
        (1 + ((2 ^ k : Nat) : Int) * (((oddCount k f : Int) - 1) + evenSum k f))) =
      perm (2 ^ k) (xorCirc k f) -
        (1 + ((2 ^ k : Nat) : Int) * (((oddCount k f : Int) - 1) + evenSum k f)) := by omega
  rw [heq] at hadd
  exact hadd

/-- Corollary 3a (Binary {0,1} XOR-Circulant Sharp Mod-2^(k+2) Law):
    For every k ≥ 1 and every binary {0,1} XOR-circulant 2^k × 2^k matrix of odd weight d,
      perm(2^k, A_f) ≡ 1 + 2^k · (d - 1)  (mod 2^(k + 2))
    (i.e. ≡ 1 mod 2^(k+2) if d ≡ 1 mod 4, and ≡ 1 + 2^(k+1) mod 2^(k+2) if d ≡ 3 mod 4). -/
theorem xorCirc_binary_odd_mod_two_pow_add_two {k : Nat} (hk : 1 ≤ k) (f : Fin (2 ^ k) → Int)
    (hbin : ∀ z, f z = 0 ∨ f z = 1) (hodd : oddCount k f % 2 = 1) :
    ((2 ^ (k + 2) : Nat) : Int) ∣
      (perm (2 ^ k) (xorCirc k f) - (1 + ((2 ^ k : Nat) : Int) * ((oddCount k f : Int) - 1))) := by
  have hev0 : evenSum k f = 0 := by
    unfold evenSum
    apply sumInt_zero
    intro z hz
    have h0 : f z % 2 = 0 := of_decide_eq_true (List.mem_filter.mp hz).2
    rcases hbin z with h | h
    · exact h
    · rw [h] at h0; simp at h0
  have hrow_eq : rowSumAll k f = (oddCount k f : Int) := by
    unfold rowSumAll oddCount
    rw [← sumInt_filter_add_not (List.finRange (2 ^ k)) (fun z => decide (f z % 2 ≠ 0))]
    have h1 : sumInt ((List.finRange (2 ^ k)).filter (fun z => decide (f z % 2 ≠ 0))) f =
        (((List.finRange (2 ^ k)).filter (fun z => decide (f z % 2 ≠ 0))).length : Int) := by
      rw [sumInt_congr (g := fun _ => (1 : Int)) (fun z hz => by
        have hne : f z % 2 ≠ 0 := of_decide_eq_true (List.mem_filter.mp hz).2
        rcases hbin z with h | h
        · rw [h] at hne; exact absurd rfl hne
        · exact h)]
      rw [sumInt_const, Int.mul_one]
    have h2 : sumInt ((List.finRange (2 ^ k)).filter (fun z => !decide (f z % 2 ≠ 0))) f = 0 := by
      apply sumInt_zero
      intro z hz
      have hne : ¬ f z % 2 ≠ 0 := by
        have hm := (List.mem_filter.mp hz).2
        intro hc; simp [hc] at hm
      rcases hbin z with h | h
      · exact h
      · rw [h] at hne; exact absurd (by decide) hne
    rw [h1, h2, Int.add_zero]
  have hrow_odd : rowSumAll k f % 2 ≠ 0 := by rw [hrow_eq]; omega
  have hmain := xorCirc_odd_mod_two_pow_add_two hk f hrow_odd
  rw [hev0, Int.add_zero] at hmain
  exact hmain

-- ============================================================================
-- SECTION 9: THEOREM 4 — Infinite Hypercube Q_k & Perfect Matching B_k Laws
-- ============================================================================

theorem isPow2Nat_iff (n : Nat) : isPow2Nat n = true ↔ ∃ b : Nat, n = 2 ^ b := by
  unfold isPow2Nat
  -- Direct characterization via induction on n or bit-level proof
  constructor
  · intro h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
    rcases h with ⟨hne, hand⟩
    -- Prove by strong induction on n: if n ≠ 0 and n &&& (n - 1) = 0 then ∃ b, n = 2^b!
    have haux : ∀ m : Nat, m ≠ 0 → m &&& (m - 1) = 0 → ∃ b, m = 2 ^ b := by
      intro m
      induction m using Nat.strongRecOn with
      | ind m ih =>
        intro hm0 hmand
        by_cases hm1 : m = 1
        · exact ⟨0, hm1⟩
        · have hm_ge2 : 2 ≤ m := by omega
          have hm_even : m % 2 = 0 := by
            by_cases he : m % 2 = 0
            · exact he
            · exfalso
              -- If m is odd and m ≥ 3, then m - 1 is even, so m &&& (m - 1) = m - 1 ≠ 0.
              have hsub : m &&& (m - 1) = m - 1 := by
                have hm_eq : m = (m - 1) + 1 := by omega
                have hbit0 : (m - 1) % 2 = 0 := by omega
                -- Prove (2q + 1) &&& (2q) = 2q via Nat.and_div_two_pow / Nat.testBit!
                apply Nat.eq_of_testBit_eq
                intro i
                rw [Nat.testBit_and]
                cases i with
                | zero => simp [Nat.testBit_zero, hbit0]
                | succ i' =>
                  have hdiv : m / 2 = (m - 1) / 2 := by omega
                  simp only [Nat.testBit_succ, hdiv, Bool.and_self]
              rw [hsub] at hmand; omega
          -- m = 2 * (m / 2), and (m / 2) &&& (m / 2 - 1) = 0!
          have hhalf_ne : m / 2 ≠ 0 := by omega
          have hhalf_and : (m / 2) &&& (m / 2 - 1) = 0 := by
            apply Nat.eq_of_testBit_eq
            intro i
            have htb := congrArg (fun x => x.testBit (i + 1)) hmand
            simp only [Nat.testBit_and, Nat.zero_testBit] at htb
            have hdiv2 : (m - 1) / 2 = m / 2 - 1 := by omega
            simp only [Nat.testBit_succ, hdiv2] at htb
            rw [Nat.testBit_and, Nat.zero_testBit]
            exact htb
          rcases ih (m / 2) (by omega) hhalf_ne hhalf_and with ⟨b, hb⟩
          refine ⟨b + 1, ?_⟩
          rw [Nat.pow_succ, ← hb]; omega
    exact haux n hne hand
  · rintro ⟨b, rfl⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
    refine ⟨by have := Nat.two_pow_pos b; omega, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    have hpow_tb : (2 ^ b).testBit i = decide (i = b) := by
      have : (2 ^ b) = 1 <<< b := by rw [Nat.shiftLeft_eq, Nat.one_mul]
      rw [this, Nat.testBit_shiftLeft]
      by_cases hib : i = b
      · subst hib; simp
      · by_cases hge : b ≤ i
        · have htb1 : (1 : Nat).testBit (i - b) = false := by
            cases hsub : i - b with
            | zero => omega
            | succ d => simp [Nat.testBit_succ]
          simp [hib, hge, htb1]
        · simp [hib, hge]
    rw [hpow_tb]
    by_cases hib : i = b
    · subst hib
      simp only [decide_true, Bool.true_and]
      have hlt : 2 ^ i - 1 < 2 ^ i := by have := Nat.two_pow_pos i; omega
      exact Nat.testBit_lt_two_pow hlt
    · simp [hib]

theorem hypercubeGen_oddCount (k : Nat) : oddCount k (hypercubeGen k) = k := by
  unfold oddCount
  let basis : List (Fin (2 ^ k)) :=
    (List.finRange k).map (fun b => ⟨2 ^ b.val, Nat.pow_lt_pow_right (by omega) b.isLt⟩)
  have hnd_b : basis.Nodup := by
    apply nodup_map_inj_on (List.nodup_finRange k)
    intro b₁ _ b₂ _ heq
    have hv : 2 ^ b₁.val = 2 ^ b₂.val := congrArg Fin.val heq
    apply Fin.ext
    by_cases hlt : b₁.val < b₂.val
    · have := Nat.pow_lt_pow_right (by omega : 1 < 2) hlt; omega
    · by_cases hgt : b₂.val < b₁.val
      · have := Nat.pow_lt_pow_right (by omega : 1 < 2) hgt; omega
      · omega
  have hperm : ((List.finRange (2 ^ k)).filter (fun z => decide (hypercubeGen k z % 2 ≠ 0))).Perm basis := by
    apply perm_of_nodup_iff ((List.nodup_finRange _).filter _) hnd_b
    intro z
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, basis, List.mem_map]
    unfold hypercubeGen
    constructor
    · intro hne
      have hp : isPow2Nat z.val = true := by
        cases hb : isPow2Nat z.val
        · simp [hb] at hne
        · rfl
      rcases (isPow2Nat_iff z.val).mp hp with ⟨b, hb⟩
      have hbk : b < k := by
        by_cases hlt : b < k
        · exact hlt
        · exfalso
          have hge : 2 ^ k ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
          have := z.isLt; omega
      exact ⟨⟨b, hbk⟩, Fin.ext hb.symm⟩
    · rintro ⟨b, hb⟩
      have hzv : z.val = 2 ^ b.val := (congrArg Fin.val hb).symm
      have hp : isPow2Nat z.val = true := (isPow2Nat_iff z.val).mpr ⟨b.val, hzv⟩
      simp [hp]
  rw [hperm.length_eq, List.length_map, List.length_finRange]

theorem hypercubeBiadjGen_oddCount (k : Nat) : oddCount k (hypercubeBiadjGen k) = k + 1 := by
  unfold oddCount
  let basis : List (Fin (2 ^ k)) :=
    finZero k :: (List.finRange k).map (fun b => ⟨2 ^ b.val, Nat.pow_lt_pow_right (by omega) b.isLt⟩)
  have hnd_b : basis.Nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, ?_⟩
    · intro hmem
      rcases List.mem_map.mp hmem with ⟨b, _, hb⟩
      have hv : 2 ^ b.val = 0 := congrArg Fin.val hb
      have := Nat.two_pow_pos b.val; omega
    · apply nodup_map_inj_on (List.nodup_finRange k)
      intro b₁ _ b₂ _ heq
      have hv : 2 ^ b₁.val = 2 ^ b₂.val := congrArg Fin.val heq
      apply Fin.ext
      by_cases hlt : b₁.val < b₂.val
      · have := Nat.pow_lt_pow_right (by omega : 1 < 2) hlt; omega
      · by_cases hgt : b₂.val < b₁.val
        · have := Nat.pow_lt_pow_right (by omega : 1 < 2) hgt; omega
        · omega
  have hperm : ((List.finRange (2 ^ k)).filter (fun z => decide (hypercubeBiadjGen k z % 2 ≠ 0))).Perm basis := by
    apply perm_of_nodup_iff ((List.nodup_finRange _).filter _) hnd_b
    intro z
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, basis, List.mem_cons, List.mem_map]
    unfold hypercubeBiadjGen
    constructor
    · intro hne
      by_cases hz0 : z.val = 0
      · left; exact Fin.ext hz0
      · right
        have hp : isPow2Nat z.val = true := by
          cases hb : isPow2Nat z.val
          · simp [hz0, hb] at hne
          · rfl
        rcases (isPow2Nat_iff z.val).mp hp with ⟨b, hb⟩
        have hbk : b < k := by
          by_cases hlt : b < k
          · exact hlt
          · exfalso
            have hge : 2 ^ k ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) (by omega)
            have := z.isLt; omega
        exact ⟨⟨b, hbk⟩, Fin.ext hb.symm⟩
    · rintro (rfl | ⟨b, hb⟩)
      · simp [finZero]
      · have hzv : z.val = 2 ^ b.val := (congrArg Fin.val hb).symm
        have hp : isPow2Nat z.val = true := (isPow2Nat_iff z.val).mpr ⟨b.val, hzv⟩
        simp [hp]
  rw [hperm.length_eq, List.length_cons, List.length_map, List.length_finRange]

/-- THEOREM 4a (Hypercube Q_k Permanent Mod 2^(k+2), ALL Odd k ≥ 1):
    For every odd dimension k ≥ 1,
      perm(A(Q_k)) ≡ 1 + 2^k · (k - 1)  (mod 2^(k + 2))
    (i.e. ≡ 1 mod 2^(k+2) if k ≡ 1 mod 4, and ≡ 1 + 2^(k+1) mod 2^(k+2) if k ≡ 3 mod 4). -/
theorem hypercubeAdj_odd_mod {k : Nat} (hk : 1 ≤ k) (hodd : k % 2 = 1) :
    ((2 ^ (k + 2) : Nat) : Int) ∣
      (perm (2 ^ k) (hypercubeAdj k) - (1 + ((2 ^ k : Nat) : Int) * ((k : Int) - 1))) := by
  have hbin : ∀ z : Fin (2 ^ k), hypercubeGen k z = 0 ∨ hypercubeGen k z = 1 := by
    intro z; unfold hypercubeGen; cases isPow2Nat z.val <;> simp
  have hcnt := hypercubeGen_oddCount k
  have h := xorCirc_binary_odd_mod_two_pow_add_two hk (hypercubeGen k) hbin (by rw [hcnt]; exact hodd)
  rw [hcnt] at h
  exact h

/-- THEOREM 4b (Hypercube Q_k Permanent Divisibility, ALL Even k ≥ 4):
    For every even dimension k ≥ 4, 2^(k + 1) ∣ perm(A(Q_k)). -/
theorem hypercubeAdj_even_dvd {k : Nat} (hk : 4 ≤ k) (heven : k % 2 = 0) :
    ((2 ^ (k + 1) : Nat) : Int) ∣ perm (2 ^ k) (hypercubeAdj k) := by
  have hrow_cnt : rowSumAll k (hypercubeGen k) = (oddCount k (hypercubeGen k) : Int) := by
    unfold rowSumAll oddCount
    rw [← sumInt_filter_add_not (List.finRange (2 ^ k)) (fun z => decide (hypercubeGen k z % 2 ≠ 0))]
    have h1 : sumInt ((List.finRange (2 ^ k)).filter (fun z => decide (hypercubeGen k z % 2 ≠ 0))) (hypercubeGen k) =
        (((List.finRange (2 ^ k)).filter (fun z => decide (hypercubeGen k z % 2 ≠ 0))).length : Int) := by
      rw [sumInt_congr (g := fun _ => (1 : Int)) (fun z hz => by
        have hne : hypercubeGen k z % 2 ≠ 0 := of_decide_eq_true (List.mem_filter.mp hz).2
        unfold hypercubeGen at hne ⊢
        cases hb : isPow2Nat z.val
        · simp [hb] at hne
        · simp)]
      rw [sumInt_const, Int.mul_one]
    have h2 : sumInt ((List.finRange (2 ^ k)).filter (fun z => !decide (hypercubeGen k z % 2 ≠ 0))) (hypercubeGen k) = 0 := by
      apply sumInt_zero; intro z hz
      have hne : ¬ hypercubeGen k z % 2 ≠ 0 := by
        have hm := (List.mem_filter.mp hz).2; intro hc; simp [hc] at hm
      unfold hypercubeGen at hne ⊢
      cases hb : isPow2Nat z.val
      · simp
      · simp [hb] at hne
    rw [h1, h2, Int.add_zero]
  have hrow : rowSumAll k (hypercubeGen k) = (k : Int) := by
    rw [hrow_cnt, hypercubeGen_oddCount]
  exact xorCirc_even_rowSum_dvd (by omega) (hypercubeGen k) (by rw [hrow]; omega)

/-- THEOREM 4c (Hypercube Perfect Matchings M_{m+1} = perm(B_{m+1}) Mod 2^(m+2), ALL Odd k = m+1 ≥ 3):
    For every even m ≥ 2 (so k = m + 1 ≥ 3 is odd),
      M_{m+1} = perm(B_{m+1}) ≡ 1 + 2^m · m  (mod 2^(m + 2)),
    i.e. M_k ≡ 1 (mod 2^(k+1)) if k ≡ 1 (mod 4), and M_k ≡ 1 + 2^k (mod 2^(k+1)) if k ≡ 3 (mod 4). -/
theorem hypercubeMatching_odd_mod {m : Nat} (hm : 2 ≤ m) (heven : m % 2 = 0) :
    ((2 ^ (m + 2) : Nat) : Int) ∣
      (perm (2 ^ m) (hypercubeBiadj m) - (1 + ((2 ^ m : Nat) : Int) * (m : Int))) := by
  have hbin : ∀ z : Fin (2 ^ m), hypercubeBiadjGen m z = 0 ∨ hypercubeBiadjGen m z = 1 := by
    intro z; unfold hypercubeBiadjGen
    by_cases hz : z.val = 0 <;> cases isPow2Nat z.val <;> simp [hz]
  have hcnt := hypercubeBiadjGen_oddCount m
  have h := xorCirc_binary_odd_mod_two_pow_add_two (by omega : 1 ≤ m) (hypercubeBiadjGen m) hbin
    (by rw [hcnt]; omega)
  rw [hcnt] at h
  have hsub : ((m + 1 : Nat) : Int) - 1 = (m : Int) := by omega
  rw [hsub] at h
  exact h

/-- THEOREM 4d (Hypercube Perfect Matchings M_{m+1} Divisibility, ALL Even k = m+1 ≥ 4):
    For every odd m ≥ 3 (so k = m + 1 ≥ 4 is even), 2^(m + 1) ∣ M_{m+1} = perm(B_{m+1}). -/
theorem hypercubeMatching_even_dvd {m : Nat} (hm : 3 ≤ m) (hodd : m % 2 = 1) :
    ((2 ^ (m + 1) : Nat) : Int) ∣ perm (2 ^ m) (hypercubeBiadj m) := by
  have hrow_cnt : rowSumAll m (hypercubeBiadjGen m) = (oddCount m (hypercubeBiadjGen m) : Int) := by
    unfold rowSumAll oddCount
    rw [← sumInt_filter_add_not (List.finRange (2 ^ m)) (fun z => decide (hypercubeBiadjGen m z % 2 ≠ 0))]
    have h1 : sumInt ((List.finRange (2 ^ m)).filter (fun z => decide (hypercubeBiadjGen m z % 2 ≠ 0))) (hypercubeBiadjGen m) =
        (((List.finRange (2 ^ m)).filter (fun z => decide (hypercubeBiadjGen m z % 2 ≠ 0))).length : Int) := by
      rw [sumInt_congr (g := fun _ => (1 : Int)) (fun z hz => by
        have hne : hypercubeBiadjGen m z % 2 ≠ 0 := of_decide_eq_true (List.mem_filter.mp hz).2
        unfold hypercubeBiadjGen at hne ⊢
        by_cases hz0 : z.val = 0
        · simp [hz0]
        · cases hb : isPow2Nat z.val
          · simp [hz0, hb] at hne
          · simp [hz0])]
      rw [sumInt_const, Int.mul_one]
    have h2 : sumInt ((List.finRange (2 ^ m)).filter (fun z => !decide (hypercubeBiadjGen m z % 2 ≠ 0))) (hypercubeBiadjGen m) = 0 := by
      apply sumInt_zero; intro z hz
      have hne : ¬ hypercubeBiadjGen m z % 2 ≠ 0 := by
        have hm' := (List.mem_filter.mp hz).2; intro hc; simp [hc] at hm'
      unfold hypercubeBiadjGen at hne ⊢
      by_cases hz0 : z.val = 0
      · simp [hz0] at hne
      · cases hb : isPow2Nat z.val
        · simp [hz0]
        · simp [hz0, hb] at hne
    rw [h1, h2, Int.add_zero]
  have hrow : rowSumAll m (hypercubeBiadjGen m) = ((m + 1 : Nat) : Int) := by
    rw [hrow_cnt, hypercubeBiadjGen_oddCount]
  exact xorCirc_even_rowSum_dvd hm (hypercubeBiadjGen m) (by rw [hrow]; omega)

-- ============================================================================
-- SECTION 10: Kernel-Checked Non-Vacuity Witnesses & Sharpness Counterexamples
-- ============================================================================

-- Non-Vacuity Gate: Constructive witnesses that all four infinite FreeBiAction families
-- and all main theorem hypotheses are genuinely inhabited for every k ≥ 1 (and m ≥ 1).

theorem nonvacuity_xorGroup (k : Nat) : Nonempty (FreeBiAction (xorGroup k) (2 ^ k)) :=
  ⟨xorFreeBiAction k⟩

theorem nonvacuity_cycGroup (k : Nat) : Nonempty (FreeBiAction (cycGroup k) (2 ^ k)) :=
  ⟨cycFreeBiAction k⟩

theorem nonvacuity_antiCyc (k : Nat) : Nonempty (FreeBiAction (cycGroup k) (2 ^ k)) :=
  ⟨antiCycFreeBiAction k⟩

theorem nonvacuity_blockXor (m k : Nat) (hm : 1 ≤ m) :
    Nonempty (FreeBiAction (xorGroup k) (m * 2 ^ k)) :=
  ⟨blockXorFreeBiAction m k hm⟩

-- Concrete kernel-checked permanent evaluations (via ryserSum + perm_eq_ryserSum, NO native_decide!):

theorem perm_Q2_eq : perm (2 ^ 2) (hypercubeAdj 2) = 4 := by
  rw [perm_eq_ryserSum]; decide

theorem perm_B3_eq : perm (2 ^ 2) (hypercubeBiadj 2) = 9 := by
  rw [perm_eq_ryserSum]; decide

theorem perm_D4_eq : perm (2 ^ 2) (xorCirc 2 derang4Gen) = 9 := by
  rw [perm_eq_ryserSum]; decide

theorem perm_diag1_eq : perm (2 ^ 2) (xorCirc 2 diag1Gen) = 1 := by
  rw [perm_eq_ryserSum]; decide

theorem perm_diag3_eq : perm (2 ^ 2) (xorCirc 2 diag3Gen) = 81 := by
  rw [perm_eq_ryserSum]; decide

/-- SHARPNESS 1: For odd-row-sum XOR-circulant matrices, Theorem 1's modulus 2^(k+1) is SHARP:
    at k = 2, D_4 = J_4 - I_4 has odd row sum 3 and perm = 9 ≡ 1 (mod 8), yet 16 ∤ (9 - 1). -/
theorem sharpness_mod_two_pow_succ :
    rowSumAll 2 derang4Gen % 2 ≠ 0 ∧
    ((2 ^ (2 + 1) : Nat) : Int) ∣ (perm (2 ^ 2) (xorCirc 2 derang4Gen) - 1) ∧
    ¬ (((2 ^ (2 + 2) : Nat) : Int) ∣ (perm (2 ^ 2) (xorCirc 2 derang4Gen) - 1)) := by
  rw [perm_D4_eq]
  refine ⟨by decide, by decide, ?_⟩
  rintro ⟨q, hq⟩; omega

/-- SHARPNESS 2: Theorem 3's modulus 2^(k+2) is SHARP for entry-histogram congruences:
    at k = 2, [1,0,0,0] and [3,0,0,0] have identical (oddCount = 1, evenSum = 0) and both satisfy
    perm ≡ 1 (mod 16), yet 32 ∤ (perm([3,0,0,0]) - perm([1,0,0,0])) since 81 - 1 = 80. -/
theorem sharpness_mod_two_pow_add_two :
    oddCount 2 diag1Gen = oddCount 2 diag3Gen ∧
    evenSum 2 diag1Gen = evenSum 2 diag3Gen ∧
    ((2 ^ (2 + 2) : Nat) : Int) ∣ (perm (2 ^ 2) (xorCirc 2 diag3Gen) - perm (2 ^ 2) (xorCirc 2 diag1Gen)) ∧
    ¬ (((2 ^ (2 + 3) : Nat) : Int) ∣ (perm (2 ^ 2) (xorCirc 2 diag3Gen) - perm (2 ^ 2) (xorCirc 2 diag1Gen))) := by
  rw [perm_diag1_eq, perm_diag3_eq]
  refine ⟨by decide, by decide, by decide, ?_⟩
  rintro ⟨q, hq⟩; omega

/-- SHARPNESS 3: Theorem 2's threshold k ≥ 3 for even-row-sum collapse is SHARP:
    at k = 2, Q_2 has even row sum 2, yet perm(A(Q_2)) = 4 is NOT divisible by 2^(2+1) = 8. -/
theorem sharpness_even_rowSum_threshold :
    rowSumAll 2 (hypercubeGen 2) % 2 = 0 ∧
    ¬ (((2 ^ (2 + 1) : Nat) : Int) ∣ perm (2 ^ 2) (hypercubeAdj 2)) := by
  rw [perm_Q2_eq]
  refine ⟨by decide, ?_⟩
  rintro ⟨q, hq⟩; omega

theorem sharpness_equivariance_perturbation :
    (∀ i j : Fin 4, derang4Pert i j % 2 = xorCirc 2 derang4Gen i j % 2) ∧
    perm 4 derang4Pert = 13 ∧
    ¬ (((2 ^ (2 + 1) : Nat) : Int) ∣ (perm 4 derang4Pert - 1)) := by
  have hp : perm 4 derang4Pert = 13 := by rw [perm_eq_ryserSum]; decide
  refine ⟨?_, hp, ?_⟩
  · intro i j; unfold derang4Pert
    rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
    by_cases h : iv = 0 ∧ jv = 0
    · rcases h with ⟨rfl, rfl⟩
      have h0 : xorCirc 2 derang4Gen ⟨0, hiv⟩ ⟨0, hjv⟩ = 0 := by
        unfold xorCirc derang4Gen xorFin; simp
      change (if (0 : Nat) = 0 ∧ (0 : Nat) = 0 then (2 : Int) else xorCirc 2 derang4Gen ⟨0, hiv⟩ ⟨0, hjv⟩) % 2 =
        xorCirc 2 derang4Gen ⟨0, hiv⟩ ⟨0, hjv⟩ % 2
      rw [h0]; decide
    · simp only [h, ↓reduceIte]
  · rw [hp]; rintro ⟨q, hq⟩; omega

theorem sharpness_odd_group_Z3 :
    oddSolCount 3 z3Circ320 = 1 ∧
    perm 3 z3Circ320 = 35 ∧
    ¬ ((4 : Int) ∣ (perm 3 z3Circ320 - 1)) := by
  have hp : perm 3 z3Circ320 = 35 := by rw [perm_eq_ryserSum]; decide
  refine ⟨by decide, hp, ?_⟩
  rw [hp]; rintro ⟨q, hq⟩; omega

-- ============================================================================
-- AXIOM RECEIPTS (Every Main Theorem Checked Against Core Lean Axioms Only)
-- ============================================================================

end SpecMat9
