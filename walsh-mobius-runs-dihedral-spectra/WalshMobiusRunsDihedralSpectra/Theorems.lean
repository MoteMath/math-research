/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WalshMobiusRunsDihedralSpectra.Defs

/-!
# Theorems (`walsh-mobius-runs-dihedral-spectra`)

Full proofs of the headline infinite theorems of Walsh-Hadamard and Boolean-Lattice Mobius Diagonalization Engine.
-/

namespace SpecMat2


/-! ## Part 1: Finite Sums, Products, Nodup Helpers, and Bijection Invariance -/

theorem nodup_map_of_inj_on {α β : Type} {l : List α} {f : α → β}
    (hnd : l.Nodup) (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have hcons := List.nodup_cons.mp hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hcons.2 (fun x hx y hy h => hinj x (List.Mem.tail _ hx) y (List.Mem.tail _ hy) h)⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨b, hb, hfb⟩
    have heq := hinj b (List.Mem.tail _ hb) a (List.Mem.head _) hfb
    exact hcons.1 (heq ▸ hb)

theorem nodup_append_of {α : Type} {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hdisj : ∀ x ∈ l₁, x ∉ l₂) : (l₁ ++ l₂).Nodup := by
  induction l₁ with
  | nil => simpa using h₂
  | cons a as ih =>
    have hc := List.nodup_cons.mp h₁
    rw [List.cons_append, List.nodup_cons]
    refine ⟨?_, ih hc.2 (fun x hx => hdisj x (List.Mem.tail _ hx))⟩
    intro hm
    rcases List.mem_append.mp hm with h | h
    · exact hc.1 h
    · exact hdisj a (List.Mem.head _) h

theorem nodup_flatMap_of {α β : Type} {l : List α} {g : α → List β}
    (hnd : l.Nodup)
    (hinner : ∀ a ∈ l, (g a).Nodup)
    (hdisj : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ y ∈ g a, y ∉ g b) : (l.flatMap g).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have hc := List.nodup_cons.mp hnd
    rw [List.flatMap_cons]
    apply nodup_append_of (hinner a (List.Mem.head _))
    · exact ih hc.2
        (fun x hx => hinner x (List.Mem.tail _ hx))
        (fun x hx y hy hne => hdisj x (List.Mem.tail _ hx) y (List.Mem.tail _ hy) hne)
    · intro y hy hm
      rcases List.mem_flatMap.mp hm with ⟨b, hb, hyb⟩
      have hne : a ≠ b := fun h => hc.1 (h ▸ hb)
      exact hdisj a (List.Mem.head _) b (List.Mem.tail _ hb) hne y hy hyb

theorem listSum_nil {α : Type} (f : α → Int) : listSum [] f = 0 := rfl

theorem listSum_cons {α : Type} (x : α) (xs : List α) (f : α → Int) :
    listSum (x :: xs) f = f x + listSum xs f := rfl

theorem listProd_nil {α : Type} (f : α → Int) : listProd [] f = 1 := rfl

theorem listProd_cons {α : Type} (x : α) (xs : List α) (f : α → Int) :
    listProd (x :: xs) f = f x * listProd xs f := rfl

theorem listSum_congr {α : Type} {l : List α} {f g : α → Int}
    (h : ∀ x ∈ l, f x = g x) : listSum l f = listSum l g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [listSum_cons]
    rw [h x (List.Mem.head _), ih (fun y hy => h y (List.Mem.tail _ hy))]

theorem listProd_congr {α : Type} {l : List α} {f g : α → Int}
    (h : ∀ x ∈ l, f x = g x) : listProd l f = listProd l g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [listProd_cons]
    rw [h x (List.Mem.head _), ih (fun y hy => h y (List.Mem.tail _ hy))]

theorem listSum_append {α : Type} (l₁ l₂ : List α) (f : α → Int) :
    listSum (l₁ ++ l₂) f = listSum l₁ f + listSum l₂ f := by
  induction l₁ with
  | nil => simp [listSum]
  | cons x xs ih => simp [listSum_cons, ih, Int.add_assoc]

theorem listProd_append {α : Type} (l₁ l₂ : List α) (f : α → Int) :
    listProd (l₁ ++ l₂) f = listProd l₁ f * listProd l₂ f := by
  induction l₁ with
  | nil => simp [listProd]
  | cons x xs ih => simp [listProd_cons, ih, Int.mul_assoc]

theorem listSum_flatMap {α β : Type} (l : List α) (g : α → List β) (f : β → Int) :
    listSum (l.flatMap g) f = listSum l (fun a => listSum (g a) f) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, listSum_append, listSum_cons, ih]

theorem listSum_add {α : Type} (l : List α) (f g : α → Int) :
    listSum l (fun x => f x + g x) = listSum l f + listSum l g := by
  induction l with
  | nil => simp [listSum]
  | cons x xs ih =>
    simp only [listSum_cons, ih]
    omega

theorem listSum_zero {α : Type} (l : List α) : listSum l (fun _ => 0) = 0 := by
  induction l with
  | nil => rfl
  | cons _ xs ih => simp [listSum_cons, ih]

theorem listSum_mul_left {α : Type} (l : List α) (c : Int) (f : α → Int) :
    listSum l (fun x => c * f x) = c * listSum l f := by
  induction l with
  | nil => simp [listSum]
  | cons x xs ih => simp [listSum_cons, ih, Int.mul_add]

theorem listSum_mul_right {α : Type} (l : List α) (f : α → Int) (c : Int) :
    listSum l (fun x => f x * c) = listSum l f * c := by
  induction l with
  | nil => simp [listSum]
  | cons x xs ih => simp [listSum_cons, ih, Int.add_mul]

theorem listSum_neg {α : Type} (l : List α) (f : α → Int) :
    listSum l (fun x => -f x) = -listSum l f := by
  induction l with
  | nil => simp [listSum]
  | cons x xs ih =>
    simp only [listSum_cons, ih]
    omega

theorem listProd_mul {α : Type} (l : List α) (f g : α → Int) :
    listProd l (fun x => f x * g x) = listProd l f * listProd l g := by
  induction l with
  | nil => simp [listProd]
  | cons x xs ih =>
    simp only [listProd_cons, ih]
    have h1 : f x * g x * (listProd xs f * listProd xs g) =
              f x * (g x * listProd xs f) * listProd xs g := by
      simp [Int.mul_assoc]
    rw [h1, Int.mul_comm (g x) (listProd xs f)]
    simp [Int.mul_assoc]

theorem listProd_one {α : Type} (l : List α) : listProd l (fun _ => 1) = 1 := by
  induction l with
  | nil => rfl
  | cons _ xs ih => simp [listProd_cons, ih]

theorem listProd_const {α : Type} (l : List α) (c : Int) :
    listProd l (fun _ => c) = c ^ l.length := by
  induction l with
  | nil => simp [listProd]
  | cons _ xs ih =>
    simp only [listProd_cons, List.length_cons, ih, Int.pow_succ, Int.mul_comm]

theorem listProd_zero_of_mem {α : Type} {l : List α} {f : α → Int} {x : α}
    (hx : x ∈ l) (hf : f x = 0) : listProd l f = 0 := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    simp only [listProd_cons]
    cases hx with
    | head => rw [hf, Int.zero_mul]
    | tail _ h => rw [ih h, Int.mul_zero]

theorem listSum_map {α β : Type} (l : List α) (φ : α → β) (f : β → Int) :
    listSum (l.map φ) f = listSum l (fun x => f (φ x)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [listSum_cons, ih]

theorem listProd_map {α β : Type} (l : List α) (φ : α → β) (f : β → Int) :
    listProd (l.map φ) f = listProd l (fun x => f (φ x)) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [listProd_cons, ih]

theorem listSum_swap {α β : Type} (l₁ : List α) (l₂ : List β) (f : α → β → Int) :
    listSum l₁ (fun a => listSum l₂ (fun b => f a b)) =
    listSum l₂ (fun b => listSum l₁ (fun a => f a b)) := by
  induction l₁ with
  | nil =>
    rw [listSum_nil]
    symm
    exact listSum_zero l₂
  | cons a as ih =>
    simp only [listSum_cons, ih, listSum_add]

theorem listSum_perm {α : Type} {l₁ l₂ : List α} (h : l₁.Perm l₂) (f : α → Int) :
    listSum l₁ f = listSum l₂ f := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [listSum_cons, ih]
  | swap x y l =>
    simp only [listSum_cons]
    omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem listProd_perm {α : Type} {l₁ l₂ : List α} (h : l₁.Perm l₂) (f : α → Int) :
    listProd l₁ f = listProd l₂ f := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [listProd_cons, ih]
  | swap x y l =>
    simp only [listProd_cons]
    rw [← Int.mul_assoc, Int.mul_comm (f y) (f x), Int.mul_assoc]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem listSum_bijection {α β : Type}
    {la : List α} {lb : List β}
    (ha : la.Nodup) (hb : lb.Nodup)
    (φ : α → β)
    (hinj : ∀ x ∈ la, ∀ y ∈ la, φ x = φ y → x = y)
    (hmem : ∀ x ∈ la, φ x ∈ lb)
    (hsurj : ∀ y ∈ lb, ∃ x ∈ la, φ x = y)
    (f : β → Int) :
    listSum la (fun x => f (φ x)) = listSum lb f := by
  rw [← listSum_map]
  have hnd : (la.map φ).Nodup := nodup_map_of_inj_on ha hinj
  have hperm : (la.map φ).Perm lb := by
    rw [List.perm_ext_iff_of_nodup hnd hb]
    intro y
    constructor
    · intro hy
      rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
      exact hmem x hx
    · intro hy
      rcases hsurj y hy with ⟨x, hx, rfl⟩
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
  exact listSum_perm hperm f

theorem listProd_bijection {α β : Type}
    {la : List α} {lb : List β}
    (ha : la.Nodup) (hb : lb.Nodup)
    (φ : α → β)
    (hinj : ∀ x ∈ la, ∀ y ∈ la, φ x = φ y → x = y)
    (hmem : ∀ x ∈ la, φ x ∈ lb)
    (hsurj : ∀ y ∈ lb, ∃ x ∈ la, φ x = y)
    (f : β → Int) :
    listProd la (fun x => f (φ x)) = listProd lb f := by
  rw [← listProd_map]
  have hnd : (la.map φ).Nodup := nodup_map_of_inj_on ha hinj
  have hperm : (la.map φ).Perm lb := by
    rw [List.perm_ext_iff_of_nodup hnd hb]
    intro y
    constructor
    · intro hy
      rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
      exact hmem x hx
    · intro hy
      rcases hsurj y hy with ⟨x, hx, rfl⟩
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
  exact listProd_perm hperm f

theorem listSum_single {α : Type} {l : List α} (hnd : l.Nodup)
    {x₀ : α} (hx₀ : x₀ ∈ l) (f : α → Int) (hzero : ∀ x ∈ l, x ≠ x₀ → f x = 0) :
    listSum l f = f x₀ := by
  induction l with
  | nil => cases hx₀
  | cons y ys ih =>
    simp only [listSum_cons]
    have hnd_cons := List.nodup_cons.mp hnd
    by_cases hy : y = x₀
    · subst hy
      have hrest : listSum ys f = 0 := by
        rw [listSum_congr (g := fun _ => 0) (fun z hz => hzero z (List.Mem.tail _ hz) (fun h => hnd_cons.1 (h ▸ hz)))]
        exact listSum_zero ys
      omega
    · have hx_ys : x₀ ∈ ys := by
        cases hx₀ with
        | head => exact absurd rfl hy
        | tail _ h => exact h
      have hfy : f y = 0 := hzero y (List.Mem.head _) hy
      rw [hfy, Int.zero_add]
      exact ih hnd_cons.2 hx_ys (fun z hz => hzero z (List.Mem.tail _ hz))

/-! ## Part 2: `Fin n` Sums/Products, Function Space `allFuncs`, and Finite Bijections -/

theorem mem_finList {n : Nat} (i : Fin n) : i ∈ finList n := List.mem_finRange i

theorem nodup_finList (n : Nat) : (finList n).Nodup := List.nodup_finRange n

theorem length_finList (n : Nat) : (finList n).length = n := List.length_finRange

theorem snocFunc_init_last {m n : Nat} (f : Fin (m + 1) → Fin n) :
    snocFunc (initFunc f) (lastFunc f) = f := by
  funext i
  simp only [snocFunc, initFunc, lastFunc]
  split
  · rfl
  · rename_i h
    have : i.val = m := by omega
    congr 1
    exact Fin.ext this.symm

theorem initFunc_snocFunc {m n : Nat} (g : Fin m → Fin n) (y : Fin n) :
    initFunc (snocFunc g y) = g := by
  funext i
  simp [initFunc, snocFunc, i.isLt]

theorem lastFunc_snocFunc {m n : Nat} (g : Fin m → Fin n) (y : Fin n) :
    lastFunc (snocFunc g y) = y := by
  simp [lastFunc, snocFunc]

theorem snocFunc_inj {m n : Nat} {g₁ g₂ : Fin m → Fin n} {y₁ y₂ : Fin n}
    (h : snocFunc g₁ y₁ = snocFunc g₂ y₂) : g₁ = g₂ ∧ y₁ = y₂ := by
  constructor
  · have := congrArg initFunc h
    simpa [initFunc_snocFunc] using this
  · have := congrArg lastFunc h
    simpa [lastFunc_snocFunc] using this

theorem mem_allFuncs {m n : Nat} (f : Fin m → Fin n) : f ∈ allFuncs n m := by
  induction m with
  | zero =>
    simp only [allFuncs, List.mem_singleton]
    funext i; exact Fin.elim0 i
  | succ m ih =>
    simp only [allFuncs, List.mem_flatMap, List.mem_map]
    exact ⟨lastFunc f, mem_finList _, initFunc f, ih (initFunc f), snocFunc_init_last f⟩

theorem nodup_allFuncs (n m : Nat) : (allFuncs n m).Nodup := by
  induction m with
  | zero => simp [allFuncs]
  | succ m ih =>
    simp only [allFuncs]
    apply nodup_flatMap_of (nodup_finList n)
    · intro y _
      exact nodup_map_of_inj_on ih (fun g₁ _ g₂ _ h => (snocFunc_inj h).1)
    · intro y₁ _ y₂ _ hne f hf₁ hf₂
      rcases List.mem_map.mp hf₁ with ⟨g₁, _, rfl⟩
      rcases List.mem_map.mp hf₂ with ⟨g₂, _, heq⟩
      exact hne (snocFunc_inj heq).2.symm

theorem finList_succ (m : Nat) :
    finList (m + 1) = (finList m).map (fun i => ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ++ [⟨m, Nat.lt_succ_self m⟩] := by
  unfold finList
  rw [List.finRange_succ_last]
  rfl

theorem prodFin_succ (m : Nat) (f : Fin (m + 1) → Int) :
    prodFin (m + 1) f = prodFin m (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) * f ⟨m, Nat.lt_succ_self m⟩ := by
  unfold prodFin
  rw [finList_succ, listProd_append, listProd_map]
  simp [listProd]

theorem prodFin_sumFin (m n : Nat) (G : Fin m → Fin n → Int) :
    prodFin m (fun i => sumFin n (fun k => G i k)) =
    listSum (allFuncs n m) (fun g => prodFin m (fun i => G i (g i))) := by
  induction m with
  | zero =>
    simp [prodFin, finList, allFuncs, listSum, listProd]
  | succ m ih =>
    rw [prodFin_succ]
    rw [ih (fun i k => G ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ k)]
    simp only [allFuncs, listSum_flatMap, listSum_map]
    unfold sumFin
    rw [← listSum_mul_left]
    apply listSum_congr
    intro y _
    rw [← listSum_mul_right]
    apply listSum_congr
    intro g _
    rw [prodFin_succ]
    simp [snocFunc]

/-! ## Part 3: Pigeonhole / Finite Injection ↔ Bijection on `Fin n` -/

theorem fin_inj_surj {n : Nat} {g : Fin n → Fin n}
    (hinj : ∀ i j, g i = g j → i = j) : ∀ y : Fin n, ∃ x : Fin n, g x = y := by
  have hnd : ((finList n).map g).Nodup :=
    nodup_map_of_inj_on (nodup_finList n) (fun x _ y _ h => hinj x y h)
  have hsub : ∀ x ∈ (finList n).map g, x ∈ finList n := fun x _ => mem_finList x
  have hlen : ((finList n).map g).length = (finList n).length := by simp
  have hperm : ((finList n).map g).Perm (finList n) := by
    have : ∀ (l₁ l₂ : List (Fin n)), l₁.Nodup → l₂.Nodup → (∀ x ∈ l₁, x ∈ l₂) → l₁.length = l₂.length → l₁.Perm l₂ := by
      intro l₁
      induction l₁ with
      | nil =>
        intro l₂ _ _ _ hl
        cases l₂ with
        | nil => exact List.Perm.nil
        | cons _ _ => simp at hl
      | cons a as ih =>
        intro l₂ hnd₁ hnd₂ hsub hl
        have ha : a ∈ l₂ := hsub a (List.Mem.head _)
        have hnd_a := List.nodup_cons.mp hnd₁
        have hperm₂ : (a :: l₂.erase a).Perm l₂ := (List.perm_cons_erase ha).symm
        have hnd_e : (l₂.erase a).Nodup := hnd₂.erase a
        have hlen_e : as.length = (l₂.erase a).length := by
          have := List.length_erase_of_mem ha
          simp at hl
          omega
        have hsub_e : ∀ x ∈ as, x ∈ l₂.erase a := by
          intro x hx
          have hne : x ≠ a := fun heq => hnd_a.1 (heq ▸ hx)
          exact (List.mem_erase_of_ne hne).mpr (hsub x (List.Mem.tail _ hx))
        exact (List.Perm.cons a (ih (l₂.erase a) hnd_a.2 hnd_e hsub_e hlen_e)).trans hperm₂
    exact this _ _ hnd (nodup_finList n) hsub hlen
  intro y
  have hy : y ∈ (finList n).map g := hperm.mem_iff.mpr (mem_finList y)
  rcases List.mem_map.mp hy with ⟨x, _, hx⟩
  exact ⟨x, hx⟩

theorem finInv_right {n : Nat} {g : Fin n → Fin n}
    (hinj : ∀ i j, g i = g j → i = j) (y : Fin n) : g (finInv g y) = y := by
  unfold finInv
  cases hfind : (finList n).find? (fun x => decide (g x = y)) with
  | some x =>
    have := List.find?_some hfind
    exact of_decide_eq_true this
  | none =>
    rcases fin_inj_surj hinj y with ⟨x, hx⟩
    have hnone := List.find?_eq_none.mp hfind x (mem_finList x)
    simp [hx] at hnone

theorem finInv_left {n : Nat} {g : Fin n → Fin n}
    (hinj : ∀ i j, g i = g j → i = j) (x : Fin n) : finInv g (g x) = x :=
  hinj _ _ (finInv_right hinj (g x))

theorem finInv_inj {n : Nat} {g : Fin n → Fin n}
    (hinj : ∀ i j, g i = g j → i = j) : ∀ y₁ y₂, finInv g y₁ = finInv g y₂ → y₁ = y₂ := by
  intro y₁ y₂ h
  have := congrArg g h
  rwa [finInv_right hinj, finInv_right hinj] at this

theorem not_inj_exists_pair {n : Nat} {f : Fin n → Fin n}
    (hnot : ¬ (∀ i j, f i = f j → i = j)) : ∃ a b : Fin n, a ≠ b ∧ f a = f b := by
  have hdec : (finList n).any (fun i => (finList n).any (fun j => decide (i ≠ j ∧ f i = f j))) = true := by
    cases h : (finList n).any (fun i => (finList n).any (fun j => decide (i ≠ j ∧ f i = f j))) with
    | true => rfl
    | false =>
      exfalso; apply hnot; intro i j hij
      have h1 : (finList n).any (fun j => decide (i ≠ j ∧ f i = f j)) = false := by
        have := List.any_eq_false.mp h i (mem_finList i)
        simpa using this
      have h2 : decide (i ≠ j ∧ f i = f j) = false := by
        have := List.any_eq_false.mp h1 j (mem_finList j)
        simpa using this
      have h3 : ¬ (i ≠ j ∧ f i = f j) := of_decide_eq_false h2
      by_cases he : i = j
      · exact he
      · exact absurd ⟨he, hij⟩ h3
  rcases List.any_eq_true.mp hdec with ⟨a, _, h1⟩
  rcases List.any_eq_true.mp h1 with ⟨b, _, h2⟩
  exact ⟨a, b, of_decide_eq_true h2⟩

/-! ## Part 4: Genuine Leibniz Determinant & Multiplicativity `det (A * B) = det A * det B` -/

theorem cmpSign_antisymm (a b : Nat) : cmpSign b a = -cmpSign a b := by
  unfold cmpSign
  split <;> split <;> omega

theorem cmpSign_self (a : Nat) : cmpSign a a = 0 := by
  simp [cmpSign]

theorem cmpSign_mul_self_of_ne {a b : Nat} (h : a ≠ b) : cmpSign a b * cmpSign a b = 1 := by
  unfold cmpSign
  split
  · rfl
  · split
    · rfl
    · omega

theorem mem_orderedPairs {n : Nat} {p : Fin n × Fin n} :
    p ∈ orderedPairs n ↔ p.1.val < p.2.val := by
  unfold orderedPairs
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨a, _, b, ⟨_, hab⟩, rfl⟩; exact hab
  · intro h; exact ⟨p.1, mem_finList _, p.2, ⟨mem_finList _, h⟩, rfl⟩

theorem nodup_orderedPairs (n : Nat) : (orderedPairs n).Nodup := by
  unfold orderedPairs
  apply nodup_flatMap_of (nodup_finList n)
  · intro i _
    exact nodup_map_of_inj_on ((nodup_finList n).filter _) (fun j₁ _ j₂ _ h => (Prod.mk.inj h).2)
  · intro i₁ _ i₂ _ hne p hp₁ hp₂
    rcases List.mem_map.mp hp₁ with ⟨j₁, _, rfl⟩
    rcases List.mem_map.mp hp₂ with ⟨j₂, _, heq⟩
    exact hne (Prod.mk.inj heq).1.symm

theorem permSign_id (n : Nat) : permSign (id : Fin n → Fin n) = 1 := by
  unfold permSign
  rw [listProd_congr (g := fun _ => 1)]
  · exact listProd_one _
  · intro p hp
    have hlt : p.1.val < p.2.val := mem_orderedPairs.mp hp
    simp [cmpSign, hlt]

theorem permSign_zero_of_not_inj {n : Nat} {f : Fin n → Fin n}
    {a b : Fin n} (hne : a ≠ b) (heq : f a = f b) : permSign f = 0 := by
  unfold permSign
  by_cases h : a.val < b.val
  · exact listProd_zero_of_mem (x := (a, b)) (mem_orderedPairs.mpr h) (by simp [heq, cmpSign_self])
  · have hba : b.val < a.val := by
      have : a.val ≠ b.val := fun hv => hne (Fin.ext hv)
      omega
    exact listProd_zero_of_mem (x := (b, a)) (mem_orderedPairs.mpr hba) (by simp [heq, cmpSign_self])

theorem permSign_comp {n : Nat} (h : Fin n → Fin n) {g : Fin n → Fin n}
    (hinj : ∀ i j, g i = g j → i = j) :
    permSign (fun i => h (g i)) = permSign g * permSign h := by
  unfold permSign
  let φ : Fin n × Fin n → Fin n × Fin n := fun p =>
    if (g p.1).val < (g p.2).val then (g p.1, g p.2) else (g p.2, g p.1)
  have hterm : ∀ p ∈ orderedPairs n,
      cmpSign (h (g p.1)).val (h (g p.2)).val =
      cmpSign (g p.1).val (g p.2).val * cmpSign (h (φ p).1).val (h (φ p).2).val := by
    intro p hp
    have hlt : p.1.val < p.2.val := mem_orderedPairs.mp hp
    have hne : (g p.1).val ≠ (g p.2).val := by
      intro heq
      have := hinj p.1 p.2 (Fin.ext heq)
      omega
    dsimp only [φ]
    by_cases hg : (g p.1).val < (g p.2).val
    · have h1 : cmpSign (g p.1).val (g p.2).val = 1 := by simp [cmpSign, hg]
      simp [hg, h1]
    · have hg2 : (g p.2).val < (g p.1).val := by omega
      have h1 : cmpSign (g p.1).val (g p.2).val = -1 := by simp [cmpSign, hg, hg2]
      simp only [hg, ↓reduceIte, h1, Int.neg_one_mul]
      rw [cmpSign_antisymm]
  rw [listProd_congr hterm, listProd_mul]
  congr 1
  exact listProd_bijection (nodup_orderedPairs n) (nodup_orderedPairs n) φ
    (by
      intro p₁ hp₁ p₂ hp₂ hφ
      have hlt₁ : p₁.1.val < p₁.2.val := mem_orderedPairs.mp hp₁
      have hlt₂ : p₂.1.val < p₂.2.val := mem_orderedPairs.mp hp₂
      dsimp only [φ] at hφ
      split at hφ <;> split at hφ
      · rcases Prod.mk.inj hφ with ⟨h1, h2⟩
        exact Prod.ext (hinj _ _ h1) (hinj _ _ h2)
      · rcases Prod.mk.inj hφ with ⟨h1, h2⟩
        have e1 := hinj _ _ h1
        have e2 := hinj _ _ h2
        omega
      · rcases Prod.mk.inj hφ with ⟨h1, h2⟩
        have e1 := hinj _ _ h1
        have e2 := hinj _ _ h2
        omega
      · rcases Prod.mk.inj hφ with ⟨h1, h2⟩
        exact Prod.ext (hinj _ _ h2) (hinj _ _ h1))
    (by
      intro p hp
      have hlt : p.1.val < p.2.val := mem_orderedPairs.mp hp
      have hne : (g p.1).val ≠ (g p.2).val := by
        intro heq
        have := hinj p.1 p.2 (Fin.ext heq)
        omega
      rw [mem_orderedPairs]
      dsimp only [φ]
      split <;> dsimp only <;> omega)
    (by
      intro q hq
      have hltq : q.1.val < q.2.val := mem_orderedPairs.mp hq
      let a := finInv g q.1
      let b := finInv g q.2
      have ha : g a = q.1 := finInv_right hinj q.1
      have hb : g b = q.2 := finInv_right hinj q.2
      have hne : a.val ≠ b.val := by
        intro heq
        have : a = b := Fin.ext heq
        rw [this] at ha
        rw [ha] at hb
        omega
      by_cases hab : a.val < b.val
      · refine ⟨(a, b), mem_orderedPairs.mpr hab, ?_⟩
        dsimp only [φ]
        rw [ha, hb]
        simp [hltq]
      · have hba : b.val < a.val := by omega
        refine ⟨(b, a), mem_orderedPairs.mpr hba, ?_⟩
        dsimp only [φ]
        rw [ha, hb]
        have hnot : ¬ q.2.val < q.1.val := by omega
        simp [hnot])
    (fun p => cmpSign (h p.1).val (h p.2).val)

theorem swapFin_invol {n : Nat} (a b i : Fin n) : swapFin a b (swapFin a b i) = i := by
  unfold swapFin
  by_cases ha : i = a
  · rw [ha]; by_cases hab : a = b <;> simp [hab]
  · by_cases hb : i = b
    · rw [hb]; simp
    · simp [ha, hb]

theorem swapFin_inj {n : Nat} (a b : Fin n) : ∀ i j, swapFin a b i = swapFin a b j → i = j := by
  intro i j h
  have := congrArg (swapFin a b) h
  simpa [swapFin_invol] using this

theorem permSign_swap {n : Nat} {a b : Fin n} (hab : a ≠ b) :
    permSign (swapFin a b) = -1 := by
  have hmain : ∀ (u v : Fin n), u.val < v.val → permSign (swapFin u v) = -1 := by
    intro u v huv
    let s1 : Fin n × Fin n → Int := fun p =>
      if p.1 = u ∧ u.val < p.2.val ∧ p.2.val < v.val then -1 else 1
    let s2 : Fin n × Fin n → Int := fun p =>
      if u.val < p.1.val ∧ p.1.val < v.val ∧ p.2 = v then -1 else 1
    let s3 : Fin n × Fin n → Int := fun p =>
      if p = (u, v) then -1 else 1
    have hfactor : ∀ p ∈ orderedPairs n,
        cmpSign (swapFin u v p.1).val (swapFin u v p.2).val = s1 p * s2 p * s3 p := by
      intro ⟨x, y⟩ hp
      have hlt : x.val < y.val := mem_orderedPairs.mp hp
      have huv_ne : u ≠ v := fun h => by rw [h] at huv; omega
      have hvu_ne : v ≠ u := huv_ne.symm
      dsimp only [s1, s2, s3, swapFin, cmpSign]
      by_cases h1u : x = u
      · rw [h1u] at hlt ⊢
        by_cases h2v : y = v
        · rw [h2v]
          have hnot : ¬ v.val < u.val := by omega
          simp [hvu_ne, huv, hnot]
        · have h2u : y ≠ u := fun h => by rw [h] at hlt; omega
          have hne_pair : (u, y) ≠ (u, v) := fun h => h2v (Prod.mk.inj h).2
          by_cases h2ltv : y.val < v.val
          · have hnot : ¬ v.val < y.val := by omega
            simp [h2u, h2v, hne_pair, hlt, h2ltv, hnot]
          · have hvlt2 : v.val < y.val := by
              have : y.val ≠ v.val := fun h => h2v (Fin.ext h)
              omega
            simp [h2u, h2v, hne_pair, h2ltv, hvlt2]
      · by_cases h1v : x = v
        · rw [h1v] at hlt ⊢
          have h2u : y ≠ u := fun h => by rw [h] at hlt; omega
          have h2v : y ≠ v := fun h => by rw [h] at hlt; omega
          have hult2 : u.val < y.val := by omega
          have hne_pair : (v, y) ≠ (u, v) := fun h => hvu_ne (Prod.mk.inj h).1
          simp [hvu_ne, h2u, h2v, hult2, hne_pair]
        · by_cases h2u : y = u
          · rw [h2u] at hlt ⊢
            have h1ltv : x.val < v.val := by omega
            have hne_pair : (x, u) ≠ (u, v) := fun h => h1u (Prod.mk.inj h).1
            simp [h1u, h1v, h1ltv, hne_pair, huv_ne]
          · by_cases h2v : y = v
            · rw [h2v] at hlt ⊢
              have hne_pair : (x, v) ≠ (u, v) := fun h => h1u (Prod.mk.inj h).1
              by_cases hult1 : u.val < x.val
              · have hnot : ¬ x.val < u.val := by omega
                simp [h1u, h1v, hvu_ne, hne_pair, hult1, hlt, hnot]
              · have h1ltu : x.val < u.val := by
                  have : x.val ≠ u.val := fun h => h1u (Fin.ext h)
                  omega
                simp [h1u, h1v, hvu_ne, hne_pair, hult1, h1ltu]
            · have hne_pair : (x, y) ≠ (u, v) := fun h => h1u (Prod.mk.inj h).1
              simp [h1u, h1v, h2u, h2v, hlt, hne_pair]
    unfold permSign
    rw [listProd_congr hfactor, listProd_mul, listProd_mul]
    have hs12 : listProd (orderedPairs n) s1 = listProd (orderedPairs n) s2 := by
      let ψ : Fin n × Fin n → Fin n × Fin n := fun p =>
        if p.1 = u ∧ u.val < p.2.val ∧ p.2.val < v.val then (p.2, v)
        else if u.val < p.1.val ∧ p.1.val < v.val ∧ p.2 = v then (u, p.1)
        else p
      have hψ_invol : ∀ p, ψ (ψ p) = p := by
        intro p
        dsimp only [ψ]
        by_cases h1 : p.1 = u ∧ u.val < p.2.val ∧ p.2.val < v.val
        · simp [h1.1, h1.2.1, h1.2.2]
          exact Prod.ext h1.1.symm rfl
        · by_cases h2 : u.val < p.1.val ∧ p.1.val < v.val ∧ p.2 = v
          · simp [h2.1, h2.2.1, h2.2.2]
            exact Prod.ext rfl h2.2.2.symm
          · simp [h1, h2]
      have hs : ∀ p ∈ orderedPairs n, s1 p = s2 (ψ p) := by
        intro p _
        dsimp only [s1, s2, ψ]
        by_cases h1 : p.1 = u ∧ u.val < p.2.val ∧ p.2.val < v.val
        · simp [h1.1, h1.2.1, h1.2.2]
        · by_cases h2 : u.val < p.1.val ∧ p.1.val < v.val ∧ p.2 = v
          · simp [h2.1, h2.2.1, h2.2.2]
          · simp [h1, h2]
      rw [listProd_congr hs]
      exact listProd_bijection (nodup_orderedPairs n) (nodup_orderedPairs n) ψ
        (fun x _ y _ h => by have := congrArg ψ h; simpa [hψ_invol] using this)
        (fun p hp => by
          have hlt : p.1.val < p.2.val := mem_orderedPairs.mp hp
          rw [mem_orderedPairs]
          dsimp only [ψ]
          split
          · rename_i h; exact h.2.2
          · split
            · rename_i h; exact h.1
            · exact hlt)
        (fun q hq => by
          refine ⟨ψ q, ?_, hψ_invol q⟩
          have hlt : q.1.val < q.2.val := mem_orderedPairs.mp hq
          rw [mem_orderedPairs]
          dsimp only [ψ]
          split
          · rename_i h; exact h.2.2
          · split
            · rename_i h; exact h.1
            · exact hlt)
        s2
    have hs2sq : listProd (orderedPairs n) s2 * listProd (orderedPairs n) s2 = 1 := by
      rw [← listProd_mul]
      rw [listProd_congr (g := fun _ => 1)]
      · exact listProd_one _
      · intro p _; dsimp only [s2]; split <;> rfl
    have hs3 : listProd (orderedPairs n) s3 = -1 := by
      have hmem : (u, v) ∈ orderedPairs n := mem_orderedPairs.mpr huv
      have hperm := List.perm_cons_erase hmem
      rw [listProd_perm hperm, listProd_cons]
      have hrest : listProd ((orderedPairs n).erase (u, v)) s3 = 1 := by
        rw [listProd_congr (g := fun _ => 1)]
        · exact listProd_one _
        · intro p hp
          have hnd := nodup_orderedPairs n
          have hne : p ≠ (u, v) := fun heq => by
            subst heq
            exact (List.nodup_cons.mp (hperm.nodup_iff.mp hnd)).1 hp
          simp [s3, hne]
      simp [s3, hrest]
    rw [hs12, hs2sq, hs3]
    rfl
  by_cases h : a.val < b.val
  · exact hmain a b h
  · have hba : b.val < a.val := by
      have : a.val ≠ b.val := fun hv => hab (Fin.ext hv)
      omega
    have hsw : swapFin a b = swapFin b a := by
      funext i; unfold swapFin
      have hba_ne : b ≠ a := hab.symm
      by_cases ha : i = a
      · rw [ha]; simp [hab]
      · by_cases hb : i = b
        · rw [hb]; simp [hba_ne]
        · simp [ha, hb]
    rw [hsw]
    exact hmain b a hba

theorem permSign_comp_swap {n : Nat} (f : Fin n → Fin n) {a b : Fin n} (hab : a ≠ b) :
    permSign (fun i => f (swapFin a b i)) = -permSign f := by
  rw [permSign_comp f (swapFin_inj a b), permSign_swap hab]
  omega

theorem det_row_pullback_zero {n : Nat} (B : Mat n) {g : Fin n → Fin n}
    {a b : Fin n} (hab : a ≠ b) (hg : g a = g b) :
    listSum (allFuncs n n) (fun f => permSign f * prodFin n (fun i => B (g i) (f i))) = 0 := by
  let S := listSum (allFuncs n n) (fun f => permSign f * prodFin n (fun i => B (g i) (f i)))
  have hneg : S = -S := by
    dsimp only [S]
    rw [← listSum_neg]
    let φ : (Fin n → Fin n) → (Fin n → Fin n) := fun f i => f (swapFin a b i)
    have hφ_invol : ∀ f, φ (φ f) = f := by
      intro f; funext i; simp [φ, swapFin_invol]
    have hbij := listSum_bijection (nodup_allFuncs n n) (nodup_allFuncs n n) φ
      (fun x _ y _ h => by have := congrArg φ h; simpa [hφ_invol] using this)
      (fun x _ => mem_allFuncs _)
      (fun y _ => ⟨φ y, mem_allFuncs _, hφ_invol y⟩)
      (fun f => permSign f * prodFin n (fun i => B (g i) (f i)))
    rw [← hbij]
    apply listSum_congr
    intro f _
    dsimp only [φ]
    rw [permSign_comp_swap f hab]
    have hprod : prodFin n (fun i => B (g i) (f (swapFin a b i))) =
                 prodFin n (fun i => B (g i) (f i)) := by
      unfold prodFin
      have hsw := listProd_bijection (nodup_finList n) (nodup_finList n) (swapFin a b)
        (fun x _ y _ h => swapFin_inj a b x y h)
        (fun x _ => mem_finList _)
        (fun y _ => ⟨swapFin a b y, mem_finList _, swapFin_invol a b y⟩)
        (fun i => B (g i) (f i))
      rw [← hsw]
      apply listProd_congr
      intro i _
      have hgsw : g (swapFin a b i) = g i := by
        unfold swapFin
        by_cases hia : i = a
        · subst hia; simp [hg]
        · by_cases hib : i = b
          · subst hib; simp [hia, hg]
          · simp [hia, hib]
      rw [hgsw]
    rw [hprod, Int.neg_mul]
  omega

theorem det_row_pullback_inj {n : Nat} (B : Mat n) {g : Fin n → Fin n}
    (hinj : ∀ i j, g i = g j → i = j) :
    listSum (allFuncs n n) (fun f => permSign f * prodFin n (fun i => B (g i) (f i))) =
    permSign g * det B := by
  unfold det
  rw [← listSum_mul_left]
  let φ : (Fin n → Fin n) → (Fin n → Fin n) := fun h i => h (g i)
  let ψ : (Fin n → Fin n) → (Fin n → Fin n) := fun f j => f (finInv g j)
  have hφψ : ∀ f, φ (ψ f) = f := fun f => by funext i; simp [φ, ψ, finInv_left hinj]
  have hψφ : ∀ h, ψ (φ h) = h := fun h => by funext j; simp [φ, ψ, finInv_right hinj]
  have hbij := listSum_bijection (nodup_allFuncs n n) (nodup_allFuncs n n) φ
    (fun x _ y _ h => by have := congrArg ψ h; simpa [hψφ] using this)
    (fun x _ => mem_allFuncs _)
    (fun y _ => ⟨ψ y, mem_allFuncs _, hφψ y⟩)
    (fun f => permSign f * prodFin n (fun i => B (g i) (f i)))
  rw [← hbij]
  apply listSum_congr
  intro h _
  dsimp only [φ]
  rw [permSign_comp h hinj, Int.mul_assoc]
  congr 1
  congr 1
  unfold prodFin
  exact listProd_bijection (nodup_finList n) (nodup_finList n) g
    (fun x _ y _ hxy => hinj x y hxy)
    (fun x _ => mem_finList _)
    (fun y _ => ⟨finInv g y, mem_finList _, finInv_right hinj y⟩)
    (fun j => B j (h j))

theorem det_mul {n : Nat} (A B : Mat n) : det (matMul A B) = det A * det B := by
  unfold det matMul
  have h1 : ∀ f : Fin n → Fin n,
      permSign f * prodFin n (fun i => sumFin n (fun k => A i k * B k (f i))) =
      listSum (allFuncs n n) (fun g => permSign f * (prodFin n (fun i => A i (g i)) * prodFin n (fun i => B (g i) (f i)))) := by
    intro f
    rw [prodFin_sumFin, ← listSum_mul_left]
    apply listSum_congr
    intro g _
    congr 1
    unfold prodFin
    exact listProd_mul (finList n) (fun i => A i (g i)) (fun i => B (g i) (f i))
  rw [listSum_congr (fun f _ => h1 f), listSum_swap]
  rw [← listSum_mul_right]
  apply listSum_congr
  intro g _
  have h2 : listSum (allFuncs n n) (fun f => permSign f * (prodFin n (fun i => A i (g i)) * prodFin n (fun i => B (g i) (f i)))) =
      prodFin n (fun i => A i (g i)) * listSum (allFuncs n n) (fun f => permSign f * prodFin n (fun i => B (g i) (f i))) := by
    rw [← listSum_mul_left]
    apply listSum_congr
    intro f _
    rw [← Int.mul_assoc, Int.mul_comm (permSign f) (prodFin n _), Int.mul_assoc]
  rw [h2]
  by_cases hinj : ∀ i j, g i = g j → i = j
  · rw [det_row_pullback_inj B hinj]
    rw [← Int.mul_assoc, Int.mul_comm (prodFin n _) (permSign g)]
    rfl
  · rcases not_inj_exists_pair hinj with ⟨a, b, hab, hgab⟩
    rw [det_row_pullback_zero B hab hgab, permSign_zero_of_not_inj hab hgab]
    simp

theorem det_diag {n : Nat} (d : Fin n → Int) : det (matDiag d) = prodFin n d := by
  unfold det
  rw [listSum_single (nodup_allFuncs n n) (mem_allFuncs id)]
  · rw [permSign_id, Int.one_mul]
    unfold prodFin matDiag
    apply listProd_congr
    intro i _
    simp
  · intro f _ hne
    have hex : ∃ i : Fin n, f i ≠ i := by
      have hdec : (finList n).any (fun i => decide (f i ≠ i)) = true := by
        cases h : (finList n).any (fun i => decide (f i ≠ i)) with
        | true => rfl
        | false =>
          exfalso; apply hne; funext i
          have h1 : decide (f i ≠ i) = false := by
            have := List.any_eq_false.mp h i (mem_finList i)
            cases hb : decide (f i ≠ i) <;> simp_all
          have h2 : ¬ (f i ≠ i) := of_decide_eq_false h1
          by_cases hi : f i = i
          · exact hi
          · exact absurd hi h2
      rcases List.any_eq_true.mp hdec with ⟨i, _, hi⟩
      exact ⟨i, of_decide_eq_true hi⟩
    rcases hex with ⟨i, hi⟩
    have hzero : prodFin n (fun j => matDiag d j (f j)) = 0 :=
      listProd_zero_of_mem (mem_finList i) (by simp [matDiag, Ne.symm hi])
    rw [hzero, Int.mul_zero]

theorem det_scale_id (n : Nat) (c : Int) : det (matScale c (matId n)) = c ^ n := by
  have heq : matScale c (matId n) = matDiag (fun _ => c) := by
    funext i j; simp [matScale, matId, matDiag]
    split <;> simp
  rw [heq, det_diag]
  unfold prodFin
  rw [listProd_const, length_finList]

theorem fin_inj_le_eq_id {n : Nat} {f : Fin n → Fin n}
    (hinj : ∀ i j, f i = f j → i = j) (hle : ∀ i, (f i).val ≤ i.val) : f = id := by
  have hstep : ∀ k : Nat, ∀ (hk : k < n), (f ⟨k, hk⟩).val = k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk
      have hle_k : (f ⟨k, hk⟩).val ≤ k := hle ⟨k, hk⟩
      by_cases hlt : (f ⟨k, hk⟩).val < k
      · let j : Fin n := ⟨(f ⟨k, hk⟩).val, by omega⟩
        have hfj : (f j).val = j.val := ih j.val hlt j.isLt
        have heq : f j = f ⟨k, hk⟩ := Fin.ext hfj
        have := hinj j ⟨k, hk⟩ heq
        have : j.val = k := congrArg Fin.val this
        omega
      · omega
  funext i
  exact Fin.ext (hstep i.val i.isLt)

theorem det_unit_lower {n : Nat} (L : Mat n)
    (hdiag : ∀ i, L i i = 1)
    (hupper : ∀ i j, i.val < j.val → L i j = 0) : det L = 1 := by
  unfold det
  rw [listSum_single (nodup_allFuncs n n) (mem_allFuncs id)]
  · rw [permSign_id, Int.one_mul]
    unfold prodFin
    dsimp only [id]
    rw [listProd_congr (g := fun _ => 1) (fun i _ => hdiag i)]
    exact listProd_one _
  · intro f _ hne
    by_cases hinj : ∀ i j, f i = f j → i = j
    · have hex : ∃ i : Fin n, i.val < (f i).val := by
        have hdec : (finList n).any (fun i => decide (i.val < (f i).val)) = true := by
          cases h : (finList n).any (fun i => decide (i.val < (f i).val)) with
          | true => rfl
          | false =>
            exfalso; apply hne
            apply fin_inj_le_eq_id hinj
            intro i
            have h1 : decide (i.val < (f i).val) = false := by
              have := List.any_eq_false.mp h i (mem_finList i)
              cases hb : decide (i.val < (f i).val) <;> simp_all
            have h2 : ¬ (i.val < (f i).val) := of_decide_eq_false h1
            omega
        rcases List.any_eq_true.mp hdec with ⟨i, _, hi⟩
        exact ⟨i, of_decide_eq_true hi⟩
      rcases hex with ⟨i, hi⟩
      have hzero : prodFin n (fun j => L j (f j)) = 0 :=
        listProd_zero_of_mem (mem_finList i) (hupper i (f i) hi)
      rw [hzero, Int.mul_zero]
    · rcases not_inj_exists_pair hinj with ⟨a, b, hab, hfab⟩
      rw [permSign_zero_of_not_inj hab hfab, Int.zero_mul]

theorem det_transpose {n : Nat} (A : Mat n) : det (matTranspose A) = det A := by
  let isInj (f : Fin n → Fin n) : Bool :=
    (finList n).all (fun i => (finList n).all (fun j => decide (f i = f j → i = j)))
  have isInj_iff : ∀ f, isInj f = true ↔ (∀ i j, f i = f j → i = j) := by
    intro f
    simp only [isInj, List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro h i j; exact h i (mem_finList i) j (mem_finList j)
    · intro h i _ j _; exact h i j
  let φ : (Fin n → Fin n) → (Fin n → Fin n) := fun f =>
    if isInj f then finInv f else f
  have hφ_invol : ∀ f, φ (φ f) = f := by
    intro f
    dsimp only [φ]
    cases h : isInj f with
    | false => simp [h]
    | true =>
      have hinj := (isInj_iff f).mp h
      have hinv_inj : isInj (finInv f) = true := (isInj_iff _).mpr (finInv_inj hinj)
      simp only [↓reduceIte, hinv_inj]
      funext i
      exact (finInv_inj hinj) _ _ (by rw [finInv_right (finInv_inj hinj), finInv_left hinj])
  unfold det
  rw [← listSum_bijection (nodup_allFuncs n n) (nodup_allFuncs n n) φ
        (fun x _ y _ h => by have := congrArg φ h; simpa [hφ_invol] using this)
        (fun x _ => mem_allFuncs _)
        (fun y _ => ⟨φ y, mem_allFuncs _, hφ_invol y⟩)]
  apply listSum_congr
  intro f _
  dsimp only [φ, matTranspose]
  cases h : isInj f with
  | false =>
    have hnot : ¬ (∀ i j, f i = f j → i = j) := fun hi => by rw [(isInj_iff f).mpr hi] at h; cases h
    rcases not_inj_exists_pair hnot with ⟨a, b, hab, hfab⟩
    simp [permSign_zero_of_not_inj hab hfab]
  | true =>
    simp only [↓reduceIte]
    have hinj := (isInj_iff f).mp h
    have hsign : permSign (finInv f) = permSign f := by
      have h1 : permSign (fun i => f (finInv f i)) = permSign (finInv f) * permSign f :=
        permSign_comp f (finInv_inj hinj)
      have h2 : (fun i => f (finInv f i)) = id := funext (finInv_right hinj)
      rw [h2, permSign_id] at h1
      have hpm : permSign f = 1 ∨ permSign f = -1 := by
        have hsq : permSign f * permSign f = 1 := by
          unfold permSign
          rw [← listProd_mul]
          rw [listProd_congr (g := fun _ => 1)]
          · exact listProd_one _
          · intro p hp
            have hlt : p.1.val < p.2.val := mem_orderedPairs.mp hp
            have hne : (f p.1).val ≠ (f p.2).val := fun heq => by
              have := hinj p.1 p.2 (Fin.ext heq); omega
            exact cmpSign_mul_self_of_ne hne
        have hfact : (permSign f - 1) * (permSign f + 1) = 0 := by
          have : (permSign f - 1) * (permSign f + 1) = permSign f * permSign f - 1 := by
            rw [Int.sub_mul, Int.mul_add, Int.mul_add]; omega
          rw [this, hsq]; rfl
        rcases Int.mul_eq_zero.mp hfact with h' | h'
        · left; omega
        · right; omega
      rcases hpm with hf | hf
      · rw [hf] at h1 ⊢; omega
      · rw [hf] at h1 ⊢; omega
    rw [hsign]
    congr 1
    unfold prodFin
    have hbij := listProd_bijection (nodup_finList n) (nodup_finList n) f
      (fun x _ y _ hxy => hinj x y hxy)
      (fun x _ => mem_finList _)
      (fun y _ => ⟨finInv f y, mem_finList _, finInv_right hinj y⟩)
      (fun j => A (finInv f j) j)
    rw [← hbij]
    apply listProd_congr
    intro i _
    rw [finInv_left hinj]

theorem det_unit_upper {n : Nat} (U : Mat n)
    (hdiag : ∀ i, U i i = 1)
    (hlower : ∀ i j, j.val < i.val → U i j = 0) : det U = 1 := by
  rw [← det_transpose]
  exact det_unit_lower (matTranspose U) hdiag (fun i j hij => hlower j i hij)

/-! ## Part 5: Bitwise Primitives & LSB Splitting on `Fin (2 ^ k)` -/

theorem popcount_zero : popcount 0 = 0 := by simp [popcount]

theorem popcount_div2_step (n : Nat) : popcount n = n % 2 + popcount (n / 2) := by
  cases n with
  | zero => simp [popcount]
  | succ m => rw [popcount]

theorem popcount_two_mul_add (q b : Nat) (hb : b < 2) :
    popcount (2 * q + b) = b + popcount q := by
  rw [popcount_div2_step]
  have hmod : (2 * q + b) % 2 = b := by omega
  have hdiv : (2 * q + b) / 2 = q := by omega
  rw [hmod, hdiv]

theorem signPow_zero : signPow 0 = 1 := rfl

theorem signPow_one : signPow 1 = -1 := rfl

theorem signPow_add (a b : Nat) : signPow (a + b) = signPow a * signPow b := by
  unfold signPow
  by_cases ha : a % 2 = 0 <;> by_cases hb : b % 2 = 0
  · have : (a + b) % 2 = 0 := by omega
    simp [ha, hb, this]
  · have : (a + b) % 2 ≠ 0 := by omega
    simp [ha, hb, this]
  · have : (a + b) % 2 ≠ 0 := by omega
    simp [ha, hb, this]
  · have : (a + b) % 2 = 0 := by omega
    simp [ha, hb, this]

theorem signPow_sq (a : Nat) : signPow a * signPow a = 1 := by
  unfold signPow; split <;> rfl

theorem signPow_two_mul (a : Nat) : signPow (2 * a) = 1 := by
  unfold signPow; simp

theorem nat_land_lt_pow2 {k x y : Nat} (hx : x < 2 ^ k) :
    x &&& y < 2 ^ k := Nat.lt_of_le_of_lt Nat.and_le_left hx

theorem nat_lor_lt_pow2 {k x y : Nat} (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    x ||| y < 2 ^ k := Nat.or_lt_two_pow hx hy

theorem testBit_false_of_lt_pow2 {x i : Nat} (h : x < 2 ^ i) : x.testBit i = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hdiv : x / 2 ^ i = 0 := Nat.div_eq_of_lt h
  simp [hdiv]

theorem nat_xor_two_mul (a b c d : Nat) (hb : b < 2) (hd : d < 2) :
    (2 * a + b) ^^^ (2 * c + d) = 2 * (a ^^^ c) + (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero =>
    rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    have h1 : (2 * a + b) % 2 = b := by omega
    have h2 : (2 * c + d) % 2 = d := by omega
    have h3 : (b ^^^ d) < 2 := Nat.xor_lt_two_pow (n := 1) hb hd
    have h4 : (2 * (a ^^^ c) + (b ^^^ d)) % 2 = b ^^^ d := by omega
    rw [h1, h2, h4]
    have hbc : b = 0 ∨ b = 1 := by omega
    have hdc : d = 0 ∨ d = 1 := by omega
    rcases hbc with rfl | rfl <;> rcases hdc with rfl | rfl <;> decide
  | succ j =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    have h1 : (2 * a + b) / 2 = a := by omega
    have h2 : (2 * c + d) / 2 = c := by omega
    have h3 : (b ^^^ d) < 2 := Nat.xor_lt_two_pow (n := 1) hb hd
    have h4 : (2 * (a ^^^ c) + (b ^^^ d)) / 2 = a ^^^ c := by omega
    rw [h1, h2, h4, Nat.testBit_xor]

theorem nat_land_two_mul (a b c d : Nat) (hb : b < 2) (hd : d < 2) :
    (2 * a + b) &&& (2 * c + d) = 2 * (a &&& c) + (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  cases i with
  | zero =>
    rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    have h1 : (2 * a + b) % 2 = b := by omega
    have h2 : (2 * c + d) % 2 = d := by omega
    have h3 : (b &&& d) < 2 := Nat.lt_of_le_of_lt Nat.and_le_left hb
    have h4 : (2 * (a &&& c) + (b &&& d)) % 2 = b &&& d := by omega
    rw [h1, h2, h4]
    have hbc : b = 0 ∨ b = 1 := by omega
    have hdc : d = 0 ∨ d = 1 := by omega
    rcases hbc with rfl | rfl <;> rcases hdc with rfl | rfl <;> decide
  | succ j =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    have h1 : (2 * a + b) / 2 = a := by omega
    have h2 : (2 * c + d) / 2 = c := by omega
    have h3 : (b &&& d) < 2 := Nat.lt_of_le_of_lt Nat.and_le_left hb
    have h4 : (2 * (a &&& c) + (b &&& d)) / 2 = a &&& c := by omega
    rw [h1, h2, h4, Nat.testBit_and]

theorem nat_lor_two_mul (a b c d : Nat) (hb : b < 2) (hd : d < 2) :
    (2 * a + b) ||| (2 * c + d) = 2 * (a ||| c) + (b ||| d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases i with
  | zero =>
    rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    have h1 : (2 * a + b) % 2 = b := by omega
    have h2 : (2 * c + d) % 2 = d := by omega
    have h3 : (b ||| d) < 2 := Nat.or_lt_two_pow (n := 1) hb hd
    have h4 : (2 * (a ||| c) + (b ||| d)) % 2 = b ||| d := by omega
    rw [h1, h2, h4]
    have hbc : b = 0 ∨ b = 1 := by omega
    have hdc : d = 0 ∨ d = 1 := by omega
    rcases hbc with rfl | rfl <;> rcases hdc with rfl | rfl <;> decide
  | succ j =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    have h1 : (2 * a + b) / 2 = a := by omega
    have h2 : (2 * c + d) / 2 = c := by omega
    have h3 : (b ||| d) < 2 := Nat.or_lt_two_pow (n := 1) hb hd
    have h4 : (2 * (a ||| c) + (b ||| d)) / 2 = a ||| c := by omega
    rw [h1, h2, h4, Nat.testBit_or]

theorem signPow_popcount_xor_and (x y u : Nat) :
    signPow (popcount ((x ^^^ y) &&& u)) =
    signPow (popcount (x &&& u)) * signPow (popcount (y &&& u)) := by
  induction u using Nat.strongRecOn generalizing x y with
  | ind u ih =>
    by_cases hu : u = 0
    · subst hu; simp [popcount_zero, signPow_zero]
    · have hlt : u / 2 < u := Nat.div_lt_self (Nat.pos_of_ne_zero hu) (by omega)
      have hx : x = 2 * (x / 2) + x % 2 := (Nat.div_add_mod x 2).symm
      have hy : y = 2 * (y / 2) + y % 2 := (Nat.div_add_mod y 2).symm
      have hu2 : u = 2 * (u / 2) + u % 2 := (Nat.div_add_mod u 2).symm
      have hxm : (x % 2) ^^^ (y % 2) < 2 := Nat.xor_lt_two_pow (n := 1) (Nat.mod_lt x (by omega)) (Nat.mod_lt y (by omega))
      have he1 : (x ^^^ y) &&& u = 2 * (((x / 2) ^^^ (y / 2)) &&& (u / 2)) + (((x % 2) ^^^ (y % 2)) &&& (u % 2)) := by
        calc (x ^^^ y) &&& u
            = ((2 * (x / 2) + x % 2) ^^^ (2 * (y / 2) + y % 2)) &&& (2 * (u / 2) + u % 2) := by
                rw [← hx, ← hy, ← hu2]
          _ = (2 * ((x / 2) ^^^ (y / 2)) + ((x % 2) ^^^ (y % 2))) &&& (2 * (u / 2) + u % 2) := by
                rw [nat_xor_two_mul _ _ _ _ (Nat.mod_lt x (by omega)) (Nat.mod_lt y (by omega))]
          _ = _ := nat_land_two_mul _ _ _ _ hxm (Nat.mod_lt u (by omega))
      have he2 : x &&& u = 2 * ((x / 2) &&& (u / 2)) + ((x % 2) &&& (u % 2)) := by
        calc x &&& u = (2 * (x / 2) + x % 2) &&& (2 * (u / 2) + u % 2) := by rw [← hx, ← hu2]
          _ = _ := nat_land_two_mul _ _ _ _ (Nat.mod_lt x (by omega)) (Nat.mod_lt u (by omega))
      have he3 : y &&& u = 2 * ((y / 2) &&& (u / 2)) + ((y % 2) &&& (u % 2)) := by
        calc y &&& u = (2 * (y / 2) + y % 2) &&& (2 * (u / 2) + u % 2) := by rw [← hy, ← hu2]
          _ = _ := nat_land_two_mul _ _ _ _ (Nat.mod_lt y (by omega)) (Nat.mod_lt u (by omega))
      have hb1 : ((x % 2) ^^^ (y % 2)) &&& (u % 2) < 2 := Nat.lt_of_le_of_lt Nat.and_le_left hxm
      have hb2 : (x % 2) &&& (u % 2) < 2 := Nat.lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt x (by omega))
      have hb3 : (y % 2) &&& (u % 2) < 2 := Nat.lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt y (by omega))
      rw [he1, he2, he3, popcount_two_mul_add _ _ hb1, popcount_two_mul_add _ _ hb2, popcount_two_mul_add _ _ hb3]
      rw [signPow_add, signPow_add, signPow_add, ih (u / 2) hlt (x / 2) (y / 2)]
      have hbit : signPow (((x % 2) ^^^ (y % 2)) &&& (u % 2)) =
                  signPow ((x % 2) &&& (u % 2)) * signPow ((y % 2) &&& (u % 2)) := by
        have hbx : x % 2 = 0 ∨ x % 2 = 1 := by omega
        have hby : y % 2 = 0 ∨ y % 2 = 1 := by omega
        have hbu : u % 2 = 0 ∨ u % 2 = 1 := by omega
        rcases hbx with h1 | h1 <;> rcases hby with h2 | h2 <;> rcases hbu with h3 | h3 <;>
          simp [h1, h2, h3, signPow]
      rw [hbit]
      have hre : ∀ a b c d : Int, (a * b) * (c * d) = (a * c) * (b * d) := by
        intro a b c d
        rw [Int.mul_assoc, ← Int.mul_assoc b c d, Int.mul_comm b c, Int.mul_assoc c b d, ← Int.mul_assoc]
      exact hre _ _ _ _

theorem fin_div2_lt {k : Nat} (x : Fin (2 ^ (k + 1))) : x.val / 2 < 2 ^ k := by
  have hx : x.val < 2 ^ k * 2 := by simpa [Nat.pow_succ] using x.isLt
  omega

theorem sumFin_pow2_succ (k : Nat) (F : Fin (2 ^ (k + 1)) → Int) :
    sumFin (2 ^ (k + 1)) F =
    sumFin (2 ^ k) (fun q => F (finEven q) + F (finOdd q)) := by
  unfold sumFin
  rw [listSum_add, ← listSum_map _ finEven, ← listSum_map _ finOdd, ← listSum_append]
  have hnd1 : ((finList (2 ^ k)).map finEven).Nodup :=
    nodup_map_of_inj_on (nodup_finList _) (fun x _ y _ h => Fin.ext (by
      have := congrArg Fin.val h; simp [finEven] at this; omega))
  have hnd2 : ((finList (2 ^ k)).map finOdd).Nodup :=
    nodup_map_of_inj_on (nodup_finList _) (fun x _ y _ h => Fin.ext (by
      have := congrArg Fin.val h; simp [finOdd] at this; omega))
  have hnd : ((finList (2 ^ k)).map finEven ++ (finList (2 ^ k)).map finOdd).Nodup := by
    apply nodup_append_of hnd1 hnd2
    intro x hx1 hx2
    rcases List.mem_map.mp hx1 with ⟨a, _, rfl⟩
    rcases List.mem_map.mp hx2 with ⟨b, _, heq⟩
    have := congrArg Fin.val heq
    simp [finEven, finOdd] at this
    omega
  have hperm : (finList (2 ^ (k + 1))).Perm ((finList (2 ^ k)).map finEven ++ (finList (2 ^ k)).map finOdd) := by
    rw [List.perm_ext_iff_of_nodup (nodup_finList _) hnd]
    intro x
    constructor
    · intro _
      rw [List.mem_append]
      by_cases hm : x.val % 2 = 0
      · left; exact List.mem_map.mpr ⟨⟨x.val / 2, fin_div2_lt x⟩, mem_finList _, Fin.ext (by simp [finEven]; omega)⟩
      · right; exact List.mem_map.mpr ⟨⟨x.val / 2, fin_div2_lt x⟩, mem_finList _, Fin.ext (by simp [finOdd]; omega)⟩
    · intro _; exact mem_finList x
  exact listSum_perm hperm F

theorem prodFin_pow2_succ (k : Nat) (F : Fin (2 ^ (k + 1)) → Int) :
    prodFin (2 ^ (k + 1)) F =
    prodFin (2 ^ k) (fun q => F (finEven q) * F (finOdd q)) := by
  unfold prodFin
  rw [listProd_mul, ← listProd_map _ finEven, ← listProd_map _ finOdd, ← listProd_append]
  have hnd1 : ((finList (2 ^ k)).map finEven).Nodup :=
    nodup_map_of_inj_on (nodup_finList _) (fun x _ y _ h => Fin.ext (by
      have := congrArg Fin.val h; simp [finEven] at this; omega))
  have hnd2 : ((finList (2 ^ k)).map finOdd).Nodup :=
    nodup_map_of_inj_on (nodup_finList _) (fun x _ y _ h => Fin.ext (by
      have := congrArg Fin.val h; simp [finOdd] at this; omega))
  have hnd : ((finList (2 ^ k)).map finEven ++ (finList (2 ^ k)).map finOdd).Nodup := by
    apply nodup_append_of hnd1 hnd2
    intro x hx1 hx2
    rcases List.mem_map.mp hx1 with ⟨a, _, rfl⟩
    rcases List.mem_map.mp hx2 with ⟨b, _, heq⟩
    have := congrArg Fin.val heq
    simp [finEven, finOdd] at this
    omega
  have hperm : (finList (2 ^ (k + 1))).Perm ((finList (2 ^ k)).map finEven ++ (finList (2 ^ k)).map finOdd) := by
    rw [List.perm_ext_iff_of_nodup (nodup_finList _) hnd]
    intro x
    constructor
    · intro _
      rw [List.mem_append]
      by_cases hm : x.val % 2 = 0
      · left; exact List.mem_map.mpr ⟨⟨x.val / 2, fin_div2_lt x⟩, mem_finList _, Fin.ext (by simp [finEven]; omega)⟩
      · right; exact List.mem_map.mpr ⟨⟨x.val / 2, fin_div2_lt x⟩, mem_finList _, Fin.ext (by simp [finOdd]; omega)⟩
    · intro _; exact mem_finList x
  exact listProd_perm hperm F

/-! ## Part 6: Engine I — Exact-Integer Walsh-Hadamard XOR-Convolution Diagonalizer -/

theorem hadamard_sq (k : Nat) :
    matMul (hadamardMat k) (hadamardMat k) = matScale ((2 : Int) ^ k) (matId (2 ^ k)) := by
  induction k with
  | zero =>
    funext u v
    have huv : u = v := Fin.ext (by omega)
    unfold matMul sumFin
    rw [listSum_single (nodup_finList 1) (mem_finList u) _ (fun w _ hne => absurd (Fin.ext (by omega)) hne)]
    simp [hadamardMat, matScale, matId, huv, popcount_zero, signPow_zero]
  | succ k ih =>
    funext u v
    unfold matMul
    rw [sumFin_pow2_succ]
    have hterm : ∀ q : Fin (2 ^ k),
        hadamardMat (k + 1) u (finEven q) * hadamardMat (k + 1) (finEven q) v +
        hadamardMat (k + 1) u (finOdd q) * hadamardMat (k + 1) (finOdd q) v =
        (1 + signPow ((u.val % 2) + (v.val % 2))) *
          (hadamardMat k ⟨u.val / 2, fin_div2_lt u⟩ q *
           hadamardMat k q ⟨v.val / 2, fin_div2_lt v⟩) := by
      intro q
      unfold hadamardMat finEven finOdd
      dsimp only
      have hu : u.val = 2 * (u.val / 2) + u.val % 2 := (Nat.div_add_mod u.val 2).symm
      have hv : v.val = 2 * (v.val / 2) + v.val % 2 := (Nat.div_add_mod v.val 2).symm
      have he0 : u.val &&& (2 * q.val) = 2 * ((u.val / 2) &&& q.val) + 0 := by
        calc u.val &&& (2 * q.val) = (2 * (u.val / 2) + u.val % 2) &&& (2 * q.val + 0) := by rw [← hu]; rfl
          _ = 2 * ((u.val / 2) &&& q.val) + ((u.val % 2) &&& 0) := nat_land_two_mul _ _ _ _ (Nat.mod_lt u.val (by omega)) (by omega)
          _ = _ := by simp
      have he1 : (2 * q.val) &&& v.val = 2 * (q.val &&& (v.val / 2)) + 0 := by
        calc (2 * q.val) &&& v.val = (2 * q.val + 0) &&& (2 * (v.val / 2) + v.val % 2) := by rw [← hv]; rfl
          _ = 2 * (q.val &&& (v.val / 2)) + (0 &&& (v.val % 2)) := nat_land_two_mul _ _ _ _ (by omega) (Nat.mod_lt v.val (by omega))
          _ = _ := by simp
      have ho0 : u.val &&& (2 * q.val + 1) = 2 * ((u.val / 2) &&& q.val) + (u.val % 2) := by
        have hm1 : (u.val % 2) &&& 1 = u.val % 2 := by
          have : u.val % 2 = 0 ∨ u.val % 2 = 1 := by omega
          rcases this with h | h <;> simp [h]
        calc u.val &&& (2 * q.val + 1) = (2 * (u.val / 2) + u.val % 2) &&& (2 * q.val + 1) := by rw [← hu]
          _ = 2 * ((u.val / 2) &&& q.val) + ((u.val % 2) &&& 1) := nat_land_two_mul _ _ _ _ (Nat.mod_lt u.val (by omega)) (by omega)
          _ = _ := by rw [hm1]
      have ho1 : (2 * q.val + 1) &&& v.val = 2 * (q.val &&& (v.val / 2)) + (v.val % 2) := by
        have hm1 : 1 &&& (v.val % 2) = v.val % 2 := by
          have : v.val % 2 = 0 ∨ v.val % 2 = 1 := by omega
          rcases this with h | h <;> simp [h]
        calc (2 * q.val + 1) &&& v.val = (2 * q.val + 1) &&& (2 * (v.val / 2) + v.val % 2) := by rw [← hv]
          _ = 2 * (q.val &&& (v.val / 2)) + (1 &&& (v.val % 2)) := nat_land_two_mul _ _ _ _ (by omega) (Nat.mod_lt v.val (by omega))
          _ = _ := by rw [hm1]
      rw [he0, he1, ho0, ho1]
      rw [popcount_two_mul_add _ 0 (by omega), popcount_two_mul_add _ 0 (by omega)]
      rw [popcount_two_mul_add _ _ (Nat.mod_lt u.val (by omega)), popcount_two_mul_add _ _ (Nat.mod_lt v.val (by omega))]
      simp only [Nat.zero_add, signPow_add]
      have halg : ∀ a b su sv : Int, a * b + (su * a) * (sv * b) = (1 + su * sv) * (a * b) := by
        intro a b su sv
        have h1 : (su * a) * (sv * b) = (su * sv) * (a * b) := by
          rw [Int.mul_assoc, ← Int.mul_assoc a sv b, Int.mul_comm a sv, Int.mul_assoc sv a b, ← Int.mul_assoc]
        rw [h1, Int.add_mul, Int.one_mul]
      exact halg _ _ _ _
    unfold sumFin
    rw [listSum_congr (fun q _ => hterm q), listSum_mul_left]
    have hih := congrFun (congrFun ih ⟨u.val / 2, fin_div2_lt u⟩) ⟨v.val / 2, fin_div2_lt v⟩
    unfold matMul sumFin at hih
    rw [hih]
    unfold matScale matId
    by_cases hmod : u.val % 2 = v.val % 2
    · have hsp : 1 + signPow (u.val % 2 + v.val % 2) = 2 := by
        unfold signPow; have : (u.val % 2 + v.val % 2) % 2 = 0 := by omega
        simp [this]
      rw [hsp]
      by_cases hdiv : u.val / 2 = v.val / 2
      · have huv : u = v := Fin.ext (by omega)
        simp [huv, Int.pow_succ, Int.mul_comm]
      · have huv : u ≠ v := fun h => hdiv (by rw [h])
        have hfin : (⟨u.val / 2, fin_div2_lt u⟩ : Fin (2 ^ k)) ≠ ⟨v.val / 2, fin_div2_lt v⟩ := fun h => hdiv (congrArg Fin.val h)
        simp [huv, hfin]
    · have hsp : 1 + signPow (u.val % 2 + v.val % 2) = 0 := by
        unfold signPow; have hodd : (u.val + v.val) % 2 ≠ 0 := by omega
        have hmod2 : (u.val % 2 + v.val % 2) % 2 = (u.val + v.val) % 2 := by omega
        rw [hmod2]; simp [hodd]
      have huv : u ≠ v := fun h => hmod (by rw [h])
      simp [hsp, huv]

theorem xorConv_mul_hadamard (k : Nat) (f : Nat → Int) :
    matMul (xorConvMat k f) (hadamardMat k) =
    matMul (hadamardMat k) (matDiag (fun u => wht k f u.val)) := by
  funext x u
  have hrhs : matMul (hadamardMat k) (matDiag (fun v => wht k f v.val)) x u =
              hadamardMat k x u * wht k f u.val := by
    unfold matMul sumFin
    rw [listSum_single (nodup_finList _) (mem_finList u)]
    · simp [matDiag]
    · intro v _ hne; simp [matDiag, hne]
  rw [hrhs]
  unfold matMul xorConvMat hadamardMat wht sumFin
  rw [← listSum_mul_left]
  let φ : Fin (2 ^ k) → Fin (2 ^ k) := fun y => ⟨x.val ^^^ y.val, nat_xor_lt_pow2 x.isLt y.isLt⟩
  have hφ_invol : ∀ y, φ (φ y) = y := fun y => Fin.ext (by
    dsimp only [φ]; rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor])
  rw [← listSum_bijection (nodup_finList _) (nodup_finList _) φ
        (fun a _ b _ h => by have := congrArg φ h; simpa [hφ_invol] using this)
        (fun a _ => mem_finList _)
        (fun b _ => ⟨φ b, mem_finList _, hφ_invol b⟩)]
  apply listSum_congr
  intro z _
  dsimp only [φ]
  have hxor : x.val ^^^ (x.val ^^^ z.val) = z.val := by
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [hxor, signPow_popcount_xor_and, Nat.and_comm z.val u.val]
  rw [Int.mul_comm (f z.val), Int.mul_assoc]

theorem hadamard_diag_xorConv (k : Nat) (f : Nat → Int) :
    matMul (hadamardMat k) (matMul (xorConvMat k f) (hadamardMat k)) =
    matScale ((2 : Int) ^ k) (matDiag (fun u => wht k f u.val)) := by
  rw [xorConv_mul_hadamard]
  have hassoc : ∀ {n : Nat} (A B C : Mat n), matMul A (matMul B C) = matMul (matMul A B) C := by
    intro n A B C; funext i j
    unfold matMul sumFin
    have h1 : ∀ k_1, A i k_1 * listSum (finList n) (fun l => B k_1 l * C l j) =
                     listSum (finList n) (fun l => A i k_1 * (B k_1 l * C l j)) :=
      fun k_1 => (listSum_mul_left _ _ _).symm
    rw [listSum_congr (fun k_1 _ => h1 k_1), listSum_swap]
    apply listSum_congr; intro l _
    rw [← listSum_mul_right]
    apply listSum_congr; intro k_1 _
    rw [Int.mul_assoc]
  rw [hassoc, hadamard_sq]
  funext i j
  unfold matMul matScale matId matDiag sumFin
  rw [listSum_single (nodup_finList _) (mem_finList i)]
  · simp
  · intro m _ hne; simp [Ne.symm hne]

theorem det_xorConv (k : Nat) (f : Nat → Int) :
    det (xorConvMat k f) = prodFin (2 ^ k) (fun u => wht k f u.val) := by
  have h1 := congrArg det (hadamard_diag_xorConv k f)
  rw [det_mul, det_mul] at h1
  have hH2 : det (hadamardMat k) * det (hadamardMat k) = ((2 : Int) ^ k) ^ (2 ^ k) := by
    have := congrArg det (hadamard_sq k)
    rw [det_mul, det_scale_id] at this
    exact this
  have hscale : det (matScale ((2 : Int) ^ k) (matDiag (n := 2 ^ k) (fun u => wht k f u.val))) =
                ((2 : Int) ^ k) ^ (2 ^ k) * prodFin (2 ^ k) (fun u => wht k f u.val) := by
    have heq : matScale ((2 : Int) ^ k) (matDiag (n := 2 ^ k) (fun u => wht k f u.val)) =
               matDiag (n := 2 ^ k) (fun u => (2 : Int) ^ k * wht k f u.val) := by
      funext i j; unfold matScale matDiag; split <;> simp
    rw [heq, det_diag]
    unfold prodFin
    rw [listProd_mul, listProd_const, length_finList]
  rw [hscale] at h1
  have hcomm : det (hadamardMat k) * (det (xorConvMat k f) * det (hadamardMat k)) =
               (det (hadamardMat k) * det (hadamardMat k)) * det (xorConvMat k f) := by
    rw [Int.mul_comm (det (xorConvMat k f)), ← Int.mul_assoc]
  rw [hcomm, hH2] at h1
  have hpos : ((2 : Int) ^ k) ^ (2 ^ k) ≠ 0 := by
    have h2 : (2 : Int) ^ k ≠ 0 := Int.pow_ne_zero (by decide)
    exact Int.pow_ne_zero h2
  exact Int.eq_of_mul_eq_mul_left hpos h1

theorem charPoly_xorConv (k : Nat) (f : Nat → Int) (lam : Int) :
    det (matSub (matScale lam (matId (2 ^ k))) (xorConvMat k f)) =
    prodFin (2 ^ k) (fun u => lam - wht k f u.val) := by
  let g : Nat → Int := fun z => (if z = 0 then lam else 0) - f z
  have hmat : matSub (matScale lam (matId (2 ^ k))) (xorConvMat k f) = xorConvMat k g := by
    funext x y
    unfold matSub matScale matId xorConvMat
    dsimp only [g]
    have hiff : x = y ↔ x.val ^^^ y.val = 0 := by
      constructor
      · intro h; rw [h, Nat.xor_self]
      · intro h
        apply Fin.ext
        have := congrArg (fun t => x.val ^^^ t) h
        rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_zero] at this
        exact this.symm
    by_cases h : x = y
    · simp [h]
    · have h2 : x.val ^^^ y.val ≠ 0 := fun hz => h (hiff.mpr hz)
      simp [h, h2]
  rw [hmat, det_xorConv]
  unfold prodFin
  apply listProd_congr
  intro u _
  unfold wht sumFin
  dsimp only [g]
  have hsplit : ∀ z : Fin (2 ^ k),
      signPow (popcount (u.val &&& z.val)) * ((if z.val = 0 then lam else 0) - f z.val) =
      (if z.val = 0 then lam else 0) + -(signPow (popcount (u.val &&& z.val)) * f z.val) := by
    intro z
    rw [Int.mul_sub]
    by_cases hz : z.val = 0
    · simp [hz, popcount_zero, signPow_zero]; omega
    · simp [hz]
  rw [listSum_congr (fun z _ => hsplit z), listSum_add, listSum_neg]
  have h0 : listSum (finList (2 ^ k)) (fun z => if z.val = 0 then lam else 0) = lam := by
    have hz0 : (⟨0, Nat.two_pow_pos k⟩ : Fin (2 ^ k)) ∈ finList (2 ^ k) := mem_finList _
    rw [listSum_single (nodup_finList _) hz0]
    · simp
    · intro z _ hne
      have : z.val ≠ 0 := fun h => hne (Fin.ext h)
      simp [this]
  rw [h0]
  omega

/-! ## Part 7: Engine II — Exact-Integer Boolean-Lattice Möbius Congruence Engine (AND & OR) -/

theorem subset_le {x y : Nat} (h : (x &&& y) = y) : y ≤ x := by
  rw [← h]; exact Nat.and_le_left

theorem subset_and_iff (x y z : Nat) :
    ((x &&& y) &&& z = z) ↔ ((x &&& z = z) ∧ (y &&& z = z)) := by
  constructor
  · intro h
    constructor
    · apply Nat.eq_of_testBit_eq; intro i
      have hi := congrArg (fun t => t.testBit i) h
      simp only [Nat.testBit_and] at hi ⊢
      cases hx : x.testBit i <;> cases hy : y.testBit i <;> cases hz : z.testBit i <;> simp_all
    · apply Nat.eq_of_testBit_eq; intro i
      have hi := congrArg (fun t => t.testBit i) h
      simp only [Nat.testBit_and] at hi ⊢
      cases hx : x.testBit i <;> cases hy : y.testBit i <;> cases hz : z.testBit i <;> simp_all
  · rintro ⟨hx, hy⟩
    rw [Nat.and_assoc, hy, hx]

theorem det_zetaMat (k : Nat) : det (zetaMat k) = 1 := by
  apply det_unit_lower
  · intro i; simp [zetaMat]
  · intro i j hij
    unfold zetaMat
    have hnot : (i.val &&& j.val) ≠ j.val := fun h => by
      have := subset_le h; omega
    simp [hnot]

/-- Exact integer inverse relation: `Z_k * μ_k = I`. -/
theorem zeta_mul_mobius (k : Nat) :
    matMul (zetaMat k) (mobiusMat k) = matId (2 ^ k) := by
  induction k with
  | zero =>
    funext x y
    have hxy : x = y := Fin.ext (by omega)
    unfold matMul sumFin
    rw [listSum_single (nodup_finList 1) (mem_finList x) _ (fun w _ hne => absurd (Fin.ext (by omega)) hne)]
    simp [zetaMat, mobiusMat, matId, hxy, popcount_zero, signPow_zero]
  | succ k ih =>
    funext x y
    unfold matMul
    rw [sumFin_pow2_succ]
    have hbit_factor : ∀ q : Fin (2 ^ k),
        zetaMat (k + 1) x (finEven q) * mobiusMat (k + 1) (finEven q) y +
        zetaMat (k + 1) x (finOdd q) * mobiusMat (k + 1) (finOdd q) y =
        (if x.val % 2 = y.val % 2 then 1 else 0) *
          (zetaMat k ⟨x.val / 2, fin_div2_lt x⟩ q *
           mobiusMat k q ⟨y.val / 2, fin_div2_lt y⟩) := by
      intro q
      unfold zetaMat mobiusMat finEven finOdd
      dsimp only
      have hx : x.val = 2 * (x.val / 2) + x.val % 2 := (Nat.div_add_mod x.val 2).symm
      have hy : y.val = 2 * (y.val / 2) + y.val % 2 := (Nat.div_add_mod y.val 2).symm
      have hsub_e1 : ((x.val &&& (2 * q.val)) = 2 * q.val) ↔ ((x.val / 2) &&& q.val = q.val) := by
        have h : x.val &&& (2 * q.val) = 2 * ((x.val / 2) &&& q.val) := by
          calc x.val &&& (2 * q.val) = (2 * (x.val / 2) + x.val % 2) &&& (2 * q.val + 0) := by rw [← hx]; rfl
            _ = 2 * ((x.val / 2) &&& q.val) + ((x.val % 2) &&& 0) := nat_land_two_mul _ _ _ _ (Nat.mod_lt x.val (by omega)) (by omega)
            _ = _ := by simp
        rw [h]; omega
      have hsub_e2 : (((2 * q.val) &&& y.val) = y.val) ↔ ((q.val &&& (y.val / 2) = y.val / 2) ∧ y.val % 2 = 0) := by
        have h : (2 * q.val) &&& y.val = 2 * (q.val &&& (y.val / 2)) := by
          calc (2 * q.val) &&& y.val = (2 * q.val + 0) &&& (2 * (y.val / 2) + y.val % 2) := by rw [← hy]; rfl
            _ = 2 * (q.val &&& (y.val / 2)) + (0 &&& (y.val % 2)) := nat_land_two_mul _ _ _ _ (by omega) (Nat.mod_lt y.val (by omega))
            _ = _ := by simp
        rw [h]; omega
      have hsub_o1 : ((x.val &&& (2 * q.val + 1)) = 2 * q.val + 1) ↔ (((x.val / 2) &&& q.val = q.val) ∧ x.val % 2 = 1) := by
        have hm1 : (x.val % 2) &&& 1 = x.val % 2 := by
          have : x.val % 2 = 0 ∨ x.val % 2 = 1 := by omega
          rcases this with h | h <;> simp [h]
        have h : x.val &&& (2 * q.val + 1) = 2 * ((x.val / 2) &&& q.val) + x.val % 2 := by
          calc x.val &&& (2 * q.val + 1) = (2 * (x.val / 2) + x.val % 2) &&& (2 * q.val + 1) := by rw [← hx]
            _ = 2 * ((x.val / 2) &&& q.val) + ((x.val % 2) &&& 1) := nat_land_two_mul _ _ _ _ (Nat.mod_lt x.val (by omega)) (by omega)
            _ = _ := by rw [hm1]
        rw [h]; omega
      have hsub_o2 : (((2 * q.val + 1) &&& y.val) = y.val) ↔ (q.val &&& (y.val / 2) = y.val / 2) := by
        have hm1 : 1 &&& (y.val % 2) = y.val % 2 := by
          have : y.val % 2 = 0 ∨ y.val % 2 = 1 := by omega
          rcases this with h | h <;> simp [h]
        have h : (2 * q.val + 1) &&& y.val = 2 * (q.val &&& (y.val / 2)) + y.val % 2 := by
          calc (2 * q.val + 1) &&& y.val = (2 * q.val + 1) &&& (2 * (y.val / 2) + y.val % 2) := by rw [← hy]
            _ = 2 * (q.val &&& (y.val / 2)) + (1 &&& (y.val % 2)) := nat_land_two_mul _ _ _ _ (by omega) (Nat.mod_lt y.val (by omega))
            _ = _ := by rw [hm1]
        rw [h]; omega
      have hpop_e : popcount ((2 * q.val) ^^^ y.val) = y.val % 2 + popcount (q.val ^^^ (y.val / 2)) := by
        have h : (2 * q.val) ^^^ y.val = 2 * (q.val ^^^ (y.val / 2)) + y.val % 2 := by
          calc (2 * q.val) ^^^ y.val = (2 * q.val + 0) ^^^ (2 * (y.val / 2) + y.val % 2) := by rw [← hy]; rfl
            _ = 2 * (q.val ^^^ (y.val / 2)) + (0 ^^^ (y.val % 2)) := nat_xor_two_mul _ _ _ _ (by omega) (Nat.mod_lt y.val (by omega))
            _ = _ := by simp
        rw [h]; exact popcount_two_mul_add _ _ (Nat.mod_lt y.val (by omega))
      have hpop_o : popcount ((2 * q.val + 1) ^^^ y.val) = (1 ^^^ (y.val % 2)) + popcount (q.val ^^^ (y.val / 2)) := by
        have h : (2 * q.val + 1) ^^^ y.val = 2 * (q.val ^^^ (y.val / 2)) + (1 ^^^ (y.val % 2)) := by
          calc (2 * q.val + 1) ^^^ y.val = (2 * q.val + 1) ^^^ (2 * (y.val / 2) + y.val % 2) := by rw [← hy]
            _ = _ := nat_xor_two_mul _ _ _ _ (by omega) (Nat.mod_lt y.val (by omega))
        rw [h]; exact popcount_two_mul_add _ _ (Nat.xor_lt_two_pow (n := 1) (by omega) (Nat.mod_lt y.val (by omega)))
      have hxm : x.val % 2 = 0 ∨ x.val % 2 = 1 := by omega
      have hym : y.val % 2 = 0 ∨ y.val % 2 = 1 := by omega
      by_cases h1 : (x.val / 2) &&& q.val = q.val <;> by_cases h2 : q.val &&& (y.val / 2) = y.val / 2
      · rcases hxm with hx0 | hx1 <;> rcases hym with hy0 | hy1
        · simp [hsub_e1, hsub_e2, hsub_o1, hsub_o2, h1, h2, hx0, hy0, hpop_e]
        · simp [hsub_e1, hsub_e2, hsub_o1, hsub_o2, h1, h2, hx0, hy1]
        · simp [hsub_e1, hsub_e2, hsub_o1, hsub_o2, h1, h2, hx1, hy0, hpop_e, hpop_o, signPow_add, signPow_one]; omega
        · simp [hsub_e1, hsub_e2, hsub_o1, hsub_o2, h1, h2, hx1, hy1, hpop_o]
      · simp [hsub_e1, hsub_e2, hsub_o1, hsub_o2, h1, h2]
      · simp [hsub_e1, hsub_e2, hsub_o1, hsub_o2, h1, h2]
      · simp [hsub_e1, hsub_e2, hsub_o1, hsub_o2, h1, h2]
    unfold sumFin
    rw [listSum_congr (fun q _ => hbit_factor q), listSum_mul_left]
    have hih := congrFun (congrFun ih ⟨x.val / 2, fin_div2_lt x⟩) ⟨y.val / 2, fin_div2_lt y⟩
    unfold matMul sumFin at hih
    rw [hih]
    unfold matId
    by_cases hm : x.val % 2 = y.val % 2
    · by_cases hd : x.val / 2 = y.val / 2
      · have hxy : x = y := Fin.ext (by omega)
        simp [hxy]
      · have hxy : x ≠ y := fun h => hd (by rw [h])
        have hfin : (⟨x.val / 2, fin_div2_lt x⟩ : Fin (2 ^ k)) ≠ ⟨y.val / 2, fin_div2_lt y⟩ := fun h => hd (congrArg Fin.val h)
        simp [hxy, hfin]
    · have hxy : x ≠ y := fun h => hm (by rw [h])
      simp [hm, hxy]

/-- Dual exact integer inverse relation: `μ_k * Z_k = I` (by `Z_k` symmetry of subsets & sign!). -/
theorem mobius_mul_zeta (k : Nat) :
    matMul (mobiusMat k) (zetaMat k) = matId (2 ^ k) := by
  funext x y
  unfold matMul sumFin
  have hterm : ∀ z : Fin (2 ^ k),
      mobiusMat k x z * zetaMat k z y =
      signPow (popcount (x.val ^^^ y.val)) * (zetaMat k x z * mobiusMat k z y) := by
    intro z
    unfold zetaMat mobiusMat
    by_cases h1 : x.val &&& z.val = z.val <;> by_cases h2 : z.val &&& y.val = y.val
    · simp only [h1, h2, ↓reduceIte, Int.mul_one, Int.one_mul]
      -- When `y ⊆ z ⊆ x`, `(x ^^^ z) + (z ^^^ y)` has disjoint bits and equals `x ^^^ y`, so popcounts add!
      have hpop : popcount (x.val ^^^ y.val) = popcount (x.val ^^^ z.val) + popcount (z.val ^^^ y.val) := by
        have haux : ∀ (a b c : Nat), a &&& b = b → b &&& c = c →
            popcount (a ^^^ c) = popcount (a ^^^ b) + popcount (b ^^^ c) := by
          intro a
          induction a using Nat.strongRecOn with
          | ind a ih =>
            intro b c hab hbc
            by_cases ha : a = 0
            · have hb : b = 0 := by have := subset_le hab; omega
              have hc : c = 0 := by have := subset_le hbc; omega
              subst ha hb hc; simp [popcount_zero]
            · have hlt : a / 2 < a := Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)
              have ha2 : a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
              have hb2 : b = 2 * (b / 2) + b % 2 := (Nat.div_add_mod b 2).symm
              have hc2 : c = 2 * (c / 2) + c % 2 := (Nat.div_add_mod c 2).symm
              have hland_ab : a &&& b = 2 * ((a / 2) &&& (b / 2)) + ((a % 2) &&& (b % 2)) := by
                calc a &&& b = (2 * (a / 2) + a % 2) &&& (2 * (b / 2) + b % 2) := by rw [← ha2, ← hb2]
                  _ = _ := nat_land_two_mul _ _ _ _ (Nat.mod_lt a (by omega)) (Nat.mod_lt b (by omega))
              have hland_bc : b &&& c = 2 * ((b / 2) &&& (c / 2)) + ((b % 2) &&& (c % 2)) := by
                calc b &&& c = (2 * (b / 2) + b % 2) &&& (2 * (c / 2) + c % 2) := by rw [← hb2, ← hc2]
                  _ = _ := nat_land_two_mul _ _ _ _ (Nat.mod_lt b (by omega)) (Nat.mod_lt c (by omega))
              have hab_div : (a / 2) &&& (b / 2) = b / 2 := by
                have hbm : (a % 2) &&& (b % 2) < 2 := Nat.lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt a (by omega))
                omega
              have hbc_div : (b / 2) &&& (c / 2) = c / 2 := by
                have hcm : (b % 2) &&& (c % 2) < 2 := Nat.lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt b (by omega))
                omega
              have hab_mod : (a % 2) &&& (b % 2) = b % 2 := by
                have hbm : (a % 2) &&& (b % 2) < 2 := Nat.lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt a (by omega))
                omega
              have hbc_mod : (b % 2) &&& (c % 2) = c % 2 := by
                have hcm : (b % 2) &&& (c % 2) < 2 := Nat.lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt b (by omega))
                omega
              have hxor_ac : a ^^^ c = 2 * ((a / 2) ^^^ (c / 2)) + ((a % 2) ^^^ (c % 2)) := by
                calc a ^^^ c = (2 * (a / 2) + a % 2) ^^^ (2 * (c / 2) + c % 2) := by rw [← ha2, ← hc2]
                  _ = _ := nat_xor_two_mul _ _ _ _ (Nat.mod_lt a (by omega)) (Nat.mod_lt c (by omega))
              have hxor_ab : a ^^^ b = 2 * ((a / 2) ^^^ (b / 2)) + ((a % 2) ^^^ (b % 2)) := by
                calc a ^^^ b = (2 * (a / 2) + a % 2) ^^^ (2 * (b / 2) + b % 2) := by rw [← ha2, ← hb2]
                  _ = _ := nat_xor_two_mul _ _ _ _ (Nat.mod_lt a (by omega)) (Nat.mod_lt b (by omega))
              have hxor_bc : b ^^^ c = 2 * ((b / 2) ^^^ (c / 2)) + ((b % 2) ^^^ (c % 2)) := by
                calc b ^^^ c = (2 * (b / 2) + b % 2) ^^^ (2 * (c / 2) + c % 2) := by rw [← hb2, ← hc2]
                  _ = _ := nat_xor_two_mul _ _ _ _ (Nat.mod_lt b (by omega)) (Nat.mod_lt c (by omega))
              rw [hxor_ac, hxor_ab, hxor_bc]
              rw [popcount_two_mul_add _ _ (Nat.xor_lt_two_pow (n := 1) (Nat.mod_lt a (by omega)) (Nat.mod_lt c (by omega)))]
              rw [popcount_two_mul_add _ _ (Nat.xor_lt_two_pow (n := 1) (Nat.mod_lt a (by omega)) (Nat.mod_lt b (by omega)))]
              rw [popcount_two_mul_add _ _ (Nat.xor_lt_two_pow (n := 1) (Nat.mod_lt b (by omega)) (Nat.mod_lt c (by omega)))]
              rw [ih (a / 2) hlt (b / 2) (c / 2) hab_div hbc_div]
              have hbit : ((a % 2) ^^^ (c % 2)) = ((a % 2) ^^^ (b % 2)) + ((b % 2) ^^^ (c % 2)) := by
                have h1 : a % 2 = 0 ∨ a % 2 = 1 := by omega
                have h2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
                have h3 : c % 2 = 0 ∨ c % 2 = 1 := by omega
                rcases h1 with ha' | ha' <;> rcases h2 with hb' | hb' <;> rcases h3 with hc' | hc' <;>
                  (rw [ha', hb'] at hab_mod; rw [hb', hc'] at hbc_mod; rw [ha', hb', hc']; try decide) <;>
                  (exfalso; revert hab_mod hbc_mod; decide)
              rw [hbit]
              simp only [Nat.pow_one]
              omega
        exact haux x.val z.val y.val h1 h2
      rw [hpop, signPow_add, Int.mul_assoc, signPow_sq, Int.mul_one]
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  rw [listSum_congr (fun z _ => hterm z), listSum_mul_left]
  have hzm := congrFun (congrFun (zeta_mul_mobius k) x) y
  unfold matMul sumFin at hzm
  rw [hzm]
  unfold matId
  by_cases hxy : x = y
  · subst hxy; simp [popcount_zero, signPow_zero]
  · simp [hxy]

theorem mobiusDown_inversion (k : Nat) (g : Nat → Int) (t : Fin (2 ^ k)) :
    sumFin (2 ^ k) (fun z => zetaMat k t z * mobiusDown k g z.val) = g t.val := by
  unfold mobiusDown sumFin
  have h1 : ∀ z : Fin (2 ^ k),
      zetaMat k t z * listSum (finList (2 ^ k)) (fun w => if z.val &&& w.val = w.val then signPow (popcount (z.val ^^^ w.val)) * g w.val else 0) =
      listSum (finList (2 ^ k)) (fun w => (zetaMat k t z * mobiusMat k z w) * g w.val) := by
    intro z
    rw [← listSum_mul_left]
    apply listSum_congr
    intro w _
    unfold mobiusMat
    split <;> simp [Int.mul_assoc]
  rw [listSum_congr (fun z _ => h1 z), listSum_swap]
  have h2 : ∀ w : Fin (2 ^ k),
      listSum (finList (2 ^ k)) (fun z => (zetaMat k t z * mobiusMat k z w) * g w.val) =
      matId (2 ^ k) t w * g w.val := by
    intro w
    rw [listSum_mul_right]
    have hzm := congrFun (congrFun (zeta_mul_mobius k) t) w
    unfold matMul sumFin at hzm
    rw [hzm]
  rw [listSum_congr (fun w _ => h2 w)]
  rw [listSum_single (nodup_finList _) (mem_finList t)]
  · simp [matId]
  · intro w _ hne; simp [matId, Ne.symm hne]

theorem andLattice_factorization (k : Nat) (g : Nat → Int) :
    andLatticeMat k g =
    matMul (matMul (zetaMat k) (matDiag (fun z => mobiusDown k g z.val))) (matTranspose (zetaMat k)) := by
  funext x y
  unfold matMul matDiag matTranspose sumFin
  have hleft : ∀ z : Fin (2 ^ k),
      listSum (finList (2 ^ k)) (fun w => zetaMat k x w * (if w = z then mobiusDown k g w.val else 0)) =
      zetaMat k x z * mobiusDown k g z.val := by
    intro z
    rw [listSum_single (nodup_finList _) (mem_finList z)]
    · simp
    · intro w _ hne; simp [hne]
  rw [listSum_congr (fun z _ => by rw [hleft z])]
  let t : Fin (2 ^ k) := ⟨x.val &&& y.val, nat_land_lt_pow2 x.isLt⟩
  have hterm : ∀ z : Fin (2 ^ k),
      (zetaMat k x z * mobiusDown k g z.val) * zetaMat k y z =
      zetaMat k t z * mobiusDown k g z.val := by
    intro z
    unfold zetaMat
    dsimp only [t]
    by_cases hx : x.val &&& z.val = z.val <;> by_cases hy : y.val &&& z.val = z.val
    · have hxy : (x.val &&& y.val) &&& z.val = z.val := (subset_and_iff x.val y.val z.val).mpr ⟨hx, hy⟩
      simp [hx, hy, hxy]
    · have hxy : ¬ ((x.val &&& y.val) &&& z.val = z.val) := fun h => hy ((subset_and_iff x.val y.val z.val).mp h).2
      simp [hx, hy, hxy]
    · have hxy : ¬ ((x.val &&& y.val) &&& z.val = z.val) := fun h => hx ((subset_and_iff x.val y.val z.val).mp h).1
      simp [hx, hy, hxy]
    · have hxy : ¬ ((x.val &&& y.val) &&& z.val = z.val) := fun h => hx ((subset_and_iff x.val y.val z.val).mp h).1
      simp [hx, hy, hxy]
  rw [listSum_congr (fun z _ => hterm z)]
  exact (mobiusDown_inversion k g t).symm

theorem det_andLattice (k : Nat) (g : Nat → Int) :
    det (andLatticeMat k g) = prodFin (2 ^ k) (fun z => mobiusDown k g z.val) := by
  rw [andLattice_factorization, det_mul, det_mul, det_transpose, det_zetaMat, det_diag]
  simp

theorem andLattice_quadForm (k : Nat) (g : Nat → Int) (v : Fin (2 ^ k) → Int) :
    quadForm (andLatticeMat k g) v =
    sumFin (2 ^ k) (fun z => mobiusDown k g z.val *
      (sumFin (2 ^ k) (fun x => zetaMat k x z * v x)) *
      (sumFin (2 ^ k) (fun y => zetaMat k y z * v y))) := by
  unfold quadForm
  have hfac := andLattice_factorization k g
  have hentry : ∀ x y : Fin (2 ^ k),
      andLatticeMat k g x y = sumFin (2 ^ k) (fun z => zetaMat k x z * mobiusDown k g z.val * zetaMat k y z) := by
    intro x y
    have h := congrFun (congrFun hfac x) y
    rw [h]
    unfold matMul matDiag matTranspose sumFin
    apply listSum_congr; intro z _
    congr 1
    rw [listSum_single (nodup_finList _) (mem_finList z)]
    · simp
    · intro w _ hne; simp [hne]
  unfold sumFin
  have h1 : ∀ x : Fin (2 ^ k),
      listSum (finList (2 ^ k)) (fun y => v x * andLatticeMat k g x y * v y) =
      listSum (finList (2 ^ k)) (fun z =>
        mobiusDown k g z.val * (zetaMat k x z * v x) *
          listSum (finList (2 ^ k)) (fun y => zetaMat k y z * v y)) := by
    intro x
    have h1a : ∀ y : Fin (2 ^ k),
        v x * andLatticeMat k g x y * v y =
        listSum (finList (2 ^ k)) (fun z => mobiusDown k g z.val * (zetaMat k x z * v x) * (zetaMat k y z * v y)) := by
      intro y
      rw [hentry x y]
      unfold sumFin
      rw [← listSum_mul_left, ← listSum_mul_right]
      apply listSum_congr; intro z _
      have hre : ∀ a b c d e : Int, a * (b * c * d) * e = c * (b * a) * (d * e) := by
        intro a b c d e
        calc a * (b * c * d) * e
            = (a * (b * c)) * (d * e) := by rw [← Int.mul_assoc, Int.mul_assoc (a * (b * c))]
          _ = (c * (b * a)) * (d * e) := by
                congr 1
                rw [Int.mul_comm a (b * c), Int.mul_assoc, Int.mul_comm c a, ← Int.mul_assoc, Int.mul_comm (b * a) c]
      exact hre (v x) (zetaMat k x z) (mobiusDown k g z.val) (zetaMat k y z) (v y)
    rw [listSum_congr (fun y _ => h1a y), listSum_swap]
    apply listSum_congr; intro z _
    rw [listSum_mul_left]
  rw [listSum_congr (fun x _ => h1 x), listSum_swap]
  apply listSum_congr; intro z _
  rw [listSum_mul_right]
  congr 1
  rw [listSum_mul_left]

/-- Exact witness evaluation: picking `v_x = mobiusMat k z₀ x` isolates `vᵀ A_k(g) v = mobiusDown k g z₀`! -/
theorem andLattice_quadForm_mobius_witness (k : Nat) (g : Nat → Int) (z₀ : Fin (2 ^ k)) :
    quadForm (andLatticeMat k g) (fun x => mobiusMat k z₀ x) = mobiusDown k g z₀.val := by
  rw [andLattice_quadForm]
  have hcol : ∀ z : Fin (2 ^ k),
      sumFin (2 ^ k) (fun x => zetaMat k x z * mobiusMat k z₀ x) =
      if z₀ = z then 1 else 0 := by
    intro z
    have hmz := congrFun (congrFun (mobius_mul_zeta k) z₀) z
    unfold matMul matId sumFin at hmz
    unfold sumFin
    rw [listSum_congr (fun x _ => Int.mul_comm (zetaMat k x z) (mobiusMat k z₀ x))]
    exact hmz
  rw [show sumFin (2 ^ k) (fun z => mobiusDown k g z.val *
      sumFin (2 ^ k) (fun x => zetaMat k x z * mobiusMat k z₀ x) *
      sumFin (2 ^ k) (fun y => zetaMat k y z * mobiusMat k z₀ y)) =
      listSum (finList (2 ^ k)) (fun z => mobiusDown k g z.val * (if z₀ = z then 1 else 0) * (if z₀ = z then 1 else 0)) from by
    unfold sumFin at hcol ⊢
    apply listSum_congr; intro z _
    rw [hcol z]]
  rw [listSum_single (nodup_finList _) (mem_finList z₀)]
  · simp
  · intro z _ hne
    have hne' : z₀ ≠ z := Ne.symm hne
    simp [hne']

theorem bitComp_invol (k : Nat) (x : Fin (2 ^ k)) : bitComp k (bitComp k x) = x :=
  Fin.ext (by dsimp only [bitComp]; rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor])

theorem bitComp_or_eq_and (k : Nat) (x y : Fin (2 ^ k)) :
    (bitComp k x).val &&& (bitComp k y).val = (bitComp k ⟨x.val ||| y.val, nat_lor_lt_pow2 x.isLt y.isLt⟩).val := by
  dsimp only [bitComp]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or]
  by_cases hi : i < k
  · have hmask : (2 ^ k - 1).testBit i = true := by
      rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hi
    rw [hmask]
    cases x.val.testBit i <;> cases y.val.testBit i <;> rfl
  · have hmask : (2 ^ k - 1).testBit i = false := by
      rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_false hi
    have hx0 : x.val.testBit i = false := testBit_false_of_lt_pow2 (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
    have hy0 : y.val.testBit i = false := testBit_false_of_lt_pow2 (Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hmask, hx0, hy0]

theorem det_orLattice (k : Nat) (g : Nat → Int) :
    det (orLatticeMat k g) = prodFin (2 ^ k) (fun z => mobiusUp k g z.val) := by
  let P : Mat (2 ^ k) := fun x y => if y = bitComp k x then 1 else 0
  have hP2 : matMul P P = matId (2 ^ k) := by
    funext x y; unfold matMul sumFin
    rw [listSum_single (nodup_finList _) (mem_finList (bitComp k x))]
    · dsimp only [P, matId]
      simp only [↓reduceIte, Int.one_mul, bitComp_invol]
      by_cases h : x = y
      · subst h; simp
      · have h2 : y ≠ x := Ne.symm h
        simp [h, h2]
    · intro w _ hne; dsimp only [P]; simp [hne]
  have hdetP2 : det P * det P = 1 := by
    have h1 := congrArg det hP2
    rw [det_mul, show matId (2 ^ k) = matScale 1 (matId (2 ^ k)) by funext i j; simp [matScale, matId]] at h1
    rw [det_scale_id, Int.one_pow] at h1
    exact h1
  let g' : Nat → Int := fun w => g ((2 ^ k - 1) ^^^ w)
  have hconj : matMul (matMul P (orLatticeMat k g)) P = andLatticeMat k g' := by
    funext x y
    unfold matMul sumFin
    have hL : ∀ z : Fin (2 ^ k),
        listSum (finList (2 ^ k)) (fun w => P x w * orLatticeMat k g w z) =
        orLatticeMat k g (bitComp k x) z := by
      intro z
      rw [listSum_single (nodup_finList _) (mem_finList (bitComp k x))]
      · dsimp only [P]; simp
      · intro w _ hne; dsimp only [P]; simp [hne]
    rw [listSum_congr (fun z _ => by rw [hL z])]
    rw [listSum_single (nodup_finList _) (mem_finList (bitComp k y))]
    · dsimp only [P, orLatticeMat, andLatticeMat, g']
      simp only [bitComp_invol, ↓reduceIte, Int.mul_one]
      congr 1
      have hdm := bitComp_or_eq_and k (bitComp k x) (bitComp k y)
      rw [bitComp_invol, bitComp_invol] at hdm
      have hxor := congrArg (fun t => (2 ^ k - 1) ^^^ t) hdm
      dsimp only [bitComp] at hxor
      rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at hxor
      exact hxor.symm
    · intro z _ hne
      dsimp only [P]
      have hne2 : y ≠ bitComp k z := fun h => hne (by rw [h, bitComp_invol])
      simp [hne2]
  have hdet_eq : det (orLatticeMat k g) = det (andLatticeMat k g') := by
    have h1 := congrArg det hconj
    rw [det_mul, det_mul] at h1
    have hr : det P * det (orLatticeMat k g) * det P = (det P * det P) * det (orLatticeMat k g) := by
      rw [Int.mul_comm (det P) (det (orLatticeMat k g)), Int.mul_assoc, Int.mul_comm (det (orLatticeMat k g))]
    rw [hr, hdetP2, Int.one_mul] at h1
    exact h1
  rw [hdet_eq, det_andLattice]
  unfold prodFin
  rw [← listProd_bijection (nodup_finList _) (nodup_finList _) (bitComp k)
        (fun a _ b _ h => by have := congrArg (bitComp k) h; simpa [bitComp_invol] using this)
        (fun a _ => mem_finList _)
        (fun b _ => ⟨bitComp k b, mem_finList _, bitComp_invol k b⟩)]
  apply listProd_congr
  intro z _
  unfold mobiusDown mobiusUp sumFin
  rw [← listSum_bijection (nodup_finList _) (nodup_finList _) (bitComp k)
        (fun a _ b _ h => by have := congrArg (bitComp k) h; simpa [bitComp_invol] using this)
        (fun a _ => mem_finList _)
        (fun b _ => ⟨bitComp k b, mem_finList _, bitComp_invol k b⟩)]
  apply listSum_congr
  intro w _
  dsimp only [g']
  have hcomp_val : (2 ^ k - 1) ^^^ (bitComp k w).val = w.val := by
    dsimp only [bitComp]; rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have hsub_iff : ((bitComp k z).val &&& (bitComp k w).val = (bitComp k w).val) ↔ (w.val &&& z.val = z.val) := by
    constructor <;> intro h <;> apply Nat.eq_of_testBit_eq <;> intro i
    · have hi := congrArg (fun t => t.testBit i) h
      dsimp only [bitComp] at hi
      simp only [Nat.testBit_and, Nat.testBit_xor] at hi ⊢
      by_cases hk : i < k
      · have hm : (2 ^ k - 1).testBit i = true := by rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hk
        rw [hm] at hi
        cases hz : z.val.testBit i <;> cases hw : w.val.testBit i <;> simp_all
      · have hz0 : z.val.testBit i = false := testBit_false_of_lt_pow2 (Nat.lt_of_lt_of_le z.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
        simp [hz0]
    · have hi := congrArg (fun t => t.testBit i) h
      dsimp only [bitComp]
      simp only [Nat.testBit_and, Nat.testBit_xor] at hi ⊢
      by_cases hk : i < k
      · have hm : (2 ^ k - 1).testBit i = true := by rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true hk
        rw [hm]
        cases hz : z.val.testBit i <;> cases hw : w.val.testBit i <;> simp_all
      · have hm : (2 ^ k - 1).testBit i = false := by rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_false hk
        have hz0 : z.val.testBit i = false := testBit_false_of_lt_pow2 (Nat.lt_of_lt_of_le z.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
        have hw0 : w.val.testBit i = false := testBit_false_of_lt_pow2 (Nat.lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
        simp [hm, hz0, hw0]
  have hxor_eq : (bitComp k z).val ^^^ (bitComp k w).val = w.val ^^^ z.val := by
    dsimp only [bitComp]
    rw [Nat.xor_comm ((2 ^ k - 1) ^^^ z.val), ← Nat.xor_assoc, Nat.xor_comm ((2 ^ k - 1) ^^^ w.val) (2 ^ k - 1),
        ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [hcomp_val, hxor_eq]
  by_cases h : w.val &&& z.val = z.val
  · have h2 := hsub_iff.mpr h
    simp [h, h2]
  · have h2 : ¬ ((bitComp k z).val &&& (bitComp k w).val = (bitComp k w).val) := fun h' => h (hsub_iff.mp h')
    simp [h, h2]

/-! ## Part 8: Reusable Finite-to-Infinite Mechanism — Bit-Slice Transfer-Matrix Compiler -/

theorem matMul_assoc {n : Nat} (A B C : Mat n) :
    matMul A (matMul B C) = matMul (matMul A B) C := by
  funext i j
  unfold matMul sumFin
  have h1 : ∀ k_1, A i k_1 * listSum (finList n) (fun l => B k_1 l * C l j) =
                   listSum (finList n) (fun l => A i k_1 * (B k_1 l * C l j)) :=
    fun k_1 => (listSum_mul_left _ _ _).symm
  rw [listSum_congr (fun k_1 _ => h1 k_1), listSum_swap]
  apply listSum_congr; intro l _
  rw [← listSum_mul_right]
  apply listSum_congr; intro k_1 _
  rw [Int.mul_assoc]

theorem matMul_id_left {n : Nat} (A : Mat n) : matMul (matId n) A = A := by
  funext i j; unfold matMul matId sumFin
  rw [listSum_single (nodup_finList _) (mem_finList i)]
  · simp
  · intro k _ hne; simp [Ne.symm hne]

theorem matMul_id_right {n : Nat} (A : Mat n) : matMul A (matId n) = A := by
  funext i j; unfold matMul matId sumFin
  rw [listSum_single (nodup_finList _) (mem_finList j)]
  · simp
  · intro k _ hne; simp [hne]

theorem matMul_add_right {n : Nat} (A B C : Mat n) :
    matMul A (matAdd B C) = matAdd (matMul A B) (matMul A C) := by
  funext i j; unfold matMul matAdd sumFin
  rw [← listSum_add]
  apply listSum_congr; intro k _
  rw [Int.mul_add]

theorem matMul_sub_right {n : Nat} (A B C : Mat n) :
    matMul A (matSub B C) = matSub (matMul A B) (matMul A C) := by
  funext i j; unfold matMul matSub sumFin
  have h : ∀ k : Fin n, A i k * (B k j - C k j) = A i k * B k j + -(A i k * C k j) := by
    intro k; rw [Int.mul_sub]; omega
  rw [listSum_congr (fun k _ => h k), listSum_add, listSum_neg]
  dsimp only; omega

theorem matMul_scale_left {n : Nat} (c : Int) (A B : Mat n) :
    matMul (matScale c A) B = matScale c (matMul A B) := by
  funext i j; unfold matMul matScale sumFin
  rw [← listSum_mul_left]
  apply listSum_congr; intro k _
  rw [Int.mul_assoc]

theorem matMul_scale_right {n : Nat} (c : Int) (A B : Mat n) :
    matMul A (matScale c B) = matScale c (matMul A B) := by
  funext i j; unfold matMul matScale sumFin
  rw [← listSum_mul_left]
  apply listSum_congr; intro k _
  rw [← Int.mul_assoc, Int.mul_comm (A i k) c, Int.mul_assoc]

theorem matScale_mul {n : Nat} (a b : Int) (A : Mat n) :
    matScale a (matScale b A) = matScale (a * b) A := by
  funext i j; unfold matScale; rw [Int.mul_assoc]

theorem contract_add {d : Nat} (α : Fin d → Int) (M₁ M₂ : Mat d) (β : Fin d → Int) :
    contract α (matAdd M₁ M₂) β = contract α M₁ β + contract α M₂ β := by
  unfold contract matAdd sumFin
  rw [← listSum_add]
  apply listSum_congr; intro i _
  rw [← listSum_add]
  apply listSum_congr; intro j _
  rw [Int.mul_add, Int.add_mul]

theorem contract_sub {d : Nat} (α : Fin d → Int) (M₁ M₂ : Mat d) (β : Fin d → Int) :
    contract α (matSub M₁ M₂) β = contract α M₁ β - contract α M₂ β := by
  unfold contract matSub sumFin
  have h1 : ∀ i : Fin d,
      listSum (finList d) (fun j => α i * (M₁ i j - M₂ i j) * β j) =
      listSum (finList d) (fun j => α i * M₁ i j * β j) + -(listSum (finList d) (fun j => α i * M₂ i j * β j)) := by
    intro i
    rw [← listSum_neg, ← listSum_add]
    apply listSum_congr; intro j _
    rw [Int.mul_sub, Int.sub_mul]; omega
  rw [listSum_congr (fun i _ => h1 i), listSum_add, listSum_neg]
  omega

theorem contract_scale {d : Nat} (α : Fin d → Int) (c : Int) (M : Mat d) (β : Fin d → Int) :
    contract α (matScale c M) β = c * contract α M β := by
  unfold contract matScale sumFin
  rw [← listSum_mul_left]
  apply listSum_congr; intro i _
  rw [← listSum_mul_left]
  apply listSum_congr; intro j _
  calc α i * (c * M i j) * β j
      = ((α i * c) * M i j) * β j := by rw [Int.mul_assoc (α i) c (M i j)]
    _ = ((c * α i) * M i j) * β j := by rw [Int.mul_comm (α i) c]
    _ = (c * (α i * M i j)) * β j := by rw [Int.mul_assoc c (α i) (M i j)]
    _ = c * (α i * M i j * β j) := by rw [Int.mul_assoc c (α i * M i j) (β j)]

/-- **ENGINE I TRANSFER COMPILER (Finite → Infinite):**
    The exact Walsh-Hadamard spectrum of ANY `d`-state bit-linear kernel on ALL `2^k` frequencies
    is compiled identically to `(T₀ + T₁, T₀ - T₁)`! -/
theorem wht_transfer_compiler {d : Nat} (A : BitAutomaton d) (k : Nat) :
    ∀ u : Nat, wht k (evalAuto A k) u = evalAuto (whtAuto A) k u := by
  -- Prove stronger matrix-level identity first (so β varies cleanly across induction!)
  have hmat : ∀ (k : Nat) (u : Nat) (β : Fin d → Int),
      wht k (fun z => contract A.α (evalWord A.T0 A.T1 k z) β) u =
      contract A.α (evalWord (matAdd A.T0 A.T1) (matSub A.T0 A.T1) k u) β := by
    intro k
    induction k with
    | zero =>
      intro u β
      unfold wht sumFin evalWord
      rw [listSum_single (nodup_finList 1) (mem_finList ⟨0, by omega⟩) _ (fun w _ hne => absurd (Fin.ext (by omega)) hne)]
      simp [popcount_zero, signPow_zero]
    | succ k ih =>
      intro u β
      unfold wht
      rw [sumFin_pow2_succ]
      let β0 : Fin d → Int := fun i => sumFin d (fun j => A.T0 i j * β j)
      let β1 : Fin d → Int := fun i => sumFin d (fun j => A.T1 i j * β j)
      have hcontr_mul : ∀ (M N : Mat d),
          contract A.α (matMul M N) β = contract A.α M (fun i => sumFin d (fun j => N i j * β j)) := by
        intro M N
        unfold contract matMul sumFin
        apply listSum_congr; intro i _
        have h1 : ∀ j : Fin d,
            A.α i * listSum (finList d) (fun l => M i l * N l j) * β j =
            listSum (finList d) (fun l => (A.α i * M i l) * (N l j * β j)) := by
          intro j
          rw [← listSum_mul_left, ← listSum_mul_right]
          apply listSum_congr; intro l _
          rw [Int.mul_assoc, Int.mul_assoc, Int.mul_assoc]
        rw [listSum_congr (fun j _ => h1 j), listSum_swap]
        apply listSum_congr; intro l _
        rw [listSum_mul_left]
      have hu : u = 2 * (u / 2) + u % 2 := (Nat.div_add_mod u 2).symm
      have hterm : ∀ q : Fin (2 ^ k),
          signPow (popcount (u &&& (finEven q).val)) * contract A.α (evalWord A.T0 A.T1 (k + 1) (finEven q).val) β +
          signPow (popcount (u &&& (finOdd q).val)) * contract A.α (evalWord A.T0 A.T1 (k + 1) (finOdd q).val) β =
          signPow (popcount ((u / 2) &&& q.val)) *
            contract A.α (evalWord A.T0 A.T1 k q.val)
              (fun i => sumFin d (fun j => (if u % 2 = 0 then matAdd A.T0 A.T1 else matSub A.T0 A.T1) i j * β j)) := by
        intro q
        dsimp only [finEven, finOdd, evalWord]
        have he_div : (2 * q.val) / 2 = q.val := by omega
        have he_mod : (2 * q.val) % 2 = 0 := by omega
        have ho_div : (2 * q.val + 1) / 2 = q.val := by omega
        have ho_mod : (2 * q.val + 1) % 2 = 1 := by omega
        have he_and : u &&& (2 * q.val) = 2 * ((u / 2) &&& q.val) + 0 := by
          calc u &&& (2 * q.val) = (2 * (u / 2) + u % 2) &&& (2 * q.val + 0) := by rw [← hu]; rfl
            _ = 2 * ((u / 2) &&& q.val) + ((u % 2) &&& 0) := nat_land_two_mul _ _ _ _ (Nat.mod_lt u (by omega)) (by omega)
            _ = _ := by simp
        have ho_and : u &&& (2 * q.val + 1) = 2 * ((u / 2) &&& q.val) + (u % 2) := by
          have hm1 : (u % 2) &&& 1 = u % 2 := by
            have : u % 2 = 0 ∨ u % 2 = 1 := by omega
            rcases this with h | h <;> simp [h]
          calc u &&& (2 * q.val + 1) = (2 * (u / 2) + u % 2) &&& (2 * q.val + 1) := by rw [← hu]
            _ = 2 * ((u / 2) &&& q.val) + ((u % 2) &&& 1) := nat_land_two_mul _ _ _ _ (Nat.mod_lt u (by omega)) (by omega)
            _ = _ := by rw [hm1]
        rw [he_div, he_mod, ho_div, ho_mod, he_and, ho_and]
        rw [popcount_two_mul_add _ 0 (by omega), popcount_two_mul_add _ _ (Nat.mod_lt u (by omega))]
        simp only [Nat.zero_add, ↓reduceIte, show (1 : Nat) ≠ 0 by omega, signPow_add]
        rw [← hcontr_mul (evalWord A.T0 A.T1 k q.val)]
        by_cases hm : u % 2 = 0
        · simp only [hm, ↓reduceIte, signPow_zero, Int.one_mul, ← Int.mul_add]
          congr 1
          rw [← contract_add, ← matMul_add_right]
        · have hm1 : u % 2 = 1 := by omega
          simp only [hm1, signPow_one, Int.neg_one_mul, show (1 : Nat) ≠ 0 by omega, ↓reduceIte]
          rw [Int.neg_mul, ← Int.mul_neg, ← Int.mul_add]
          congr 1
          rw [← Int.sub_eq_add_neg, ← contract_sub, ← matMul_sub_right]
      change listSum (finList (2 ^ k)) _ = _
      rw [listSum_congr (fun q _ => hterm q)]
      have hstep := ih (u / 2) (fun i => sumFin d (fun j => (if u % 2 = 0 then matAdd A.T0 A.T1 else matSub A.T0 A.T1) i j * β j))
      unfold wht at hstep
      change listSum (finList (2 ^ k)) _ = _ at hstep
      rw [hstep, ← hcontr_mul]
      rfl
  intro u
  exact hmat k u A.β

/-- **ENGINE II TRANSFER COMPILER (AND-Lattice Boolean Möbius, Finite → Infinite):**
    The exact downward Boolean Möbius spectrum of ANY `d`-state bit-linear kernel on ALL `2^k` elements
    is compiled identically to `(T₀, T₁ - T₀)`! -/
theorem mobiusDown_transfer_compiler {d : Nat} (A : BitAutomaton d) (k : Nat) :
    ∀ z : Nat, z < 2 ^ k → mobiusDown k (evalAuto A k) z = evalAuto (mobiusDownAuto A) k z := by
  have hmat : ∀ (k : Nat) (z : Nat), z < 2 ^ k → ∀ (β : Fin d → Int),
      mobiusDown k (fun w => contract A.α (evalWord A.T0 A.T1 k w) β) z =
      contract A.α (evalWord A.T0 (matSub A.T1 A.T0) k z) β := by
    intro k
    induction k with
    | zero =>
      intro z hz β
      have hz0 : z = 0 := by omega
      subst hz0
      unfold mobiusDown sumFin evalWord
      rw [listSum_single (nodup_finList 1) (mem_finList ⟨0, by omega⟩) _ (fun w _ hne => absurd (Fin.ext (by omega)) hne)]
      simp [popcount_zero, signPow_zero]
    | succ k ih =>
      intro z hz_lt β
      have hz2 : z / 2 < 2 ^ k := by rw [Nat.pow_succ] at hz_lt; omega
      unfold mobiusDown
      rw [sumFin_pow2_succ]
      have hcontr_mul : ∀ (M N : Mat d),
          contract A.α (matMul M N) β = contract A.α M (fun i => sumFin d (fun j => N i j * β j)) := by
        intro M N
        unfold contract matMul sumFin
        apply listSum_congr; intro i _
        have h1 : ∀ j : Fin d,
            A.α i * listSum (finList d) (fun l => M i l * N l j) * β j =
            listSum (finList d) (fun l => (A.α i * M i l) * (N l j * β j)) := by
          intro j
          rw [← listSum_mul_left, ← listSum_mul_right]
          apply listSum_congr; intro l _
          rw [Int.mul_assoc, Int.mul_assoc, Int.mul_assoc]
        rw [listSum_congr (fun j _ => h1 j), listSum_swap]
        apply listSum_congr; intro l _
        rw [listSum_mul_left]
      have hz : z = 2 * (z / 2) + z % 2 := (Nat.div_add_mod z 2).symm
      have hterm : ∀ q : Fin (2 ^ k),
          (if z &&& (finEven q).val = (finEven q).val then signPow (popcount (z ^^^ (finEven q).val)) * contract A.α (evalWord A.T0 A.T1 (k + 1) (finEven q).val) β else 0) +
          (if z &&& (finOdd q).val = (finOdd q).val then signPow (popcount (z ^^^ (finOdd q).val)) * contract A.α (evalWord A.T0 A.T1 (k + 1) (finOdd q).val) β else 0) =
          if (z / 2) &&& q.val = q.val then
            signPow (popcount ((z / 2) ^^^ q.val)) *
              contract A.α (evalWord A.T0 A.T1 k q.val)
                (fun i => sumFin d (fun j => (if z % 2 = 0 then A.T0 else matSub A.T1 A.T0) i j * β j))
          else 0 := by
        intro q
        dsimp only [finEven, finOdd, evalWord]
        have he_div : (2 * q.val) / 2 = q.val := by omega
        have he_mod : (2 * q.val) % 2 = 0 := by omega
        have ho_div : (2 * q.val + 1) / 2 = q.val := by omega
        have ho_mod : (2 * q.val + 1) % 2 = 1 := by omega
        have hsub_e : (z &&& (2 * q.val) = 2 * q.val) ↔ ((z / 2) &&& q.val = q.val) := by
          have h : z &&& (2 * q.val) = 2 * ((z / 2) &&& q.val) := by
            calc z &&& (2 * q.val) = (2 * (z / 2) + z % 2) &&& (2 * q.val + 0) := by rw [← hz]; rfl
              _ = 2 * ((z / 2) &&& q.val) + ((z % 2) &&& 0) := nat_land_two_mul _ _ _ _ (Nat.mod_lt z (by omega)) (by omega)
              _ = _ := by simp
          rw [h]; omega
        have hsub_o : (z &&& (2 * q.val + 1) = 2 * q.val + 1) ↔ (((z / 2) &&& q.val = q.val) ∧ z % 2 = 1) := by
          have hm1 : (z % 2) &&& 1 = z % 2 := by
            have : z % 2 = 0 ∨ z % 2 = 1 := by omega
            rcases this with h | h <;> simp [h]
          have h : z &&& (2 * q.val + 1) = 2 * ((z / 2) &&& q.val) + z % 2 := by
            calc z &&& (2 * q.val + 1) = (2 * (z / 2) + z % 2) &&& (2 * q.val + 1) := by rw [← hz]
              _ = 2 * ((z / 2) &&& q.val) + ((z % 2) &&& 1) := nat_land_two_mul _ _ _ _ (Nat.mod_lt z (by omega)) (by omega)
              _ = _ := by rw [hm1]
          rw [h]; omega
        have hpop_e : popcount (z ^^^ (2 * q.val)) = z % 2 + popcount ((z / 2) ^^^ q.val) := by
          have h : z ^^^ (2 * q.val) = 2 * ((z / 2) ^^^ q.val) + z % 2 := by
            calc z ^^^ (2 * q.val) = (2 * (z / 2) + z % 2) ^^^ (2 * q.val + 0) := by rw [← hz]; rfl
              _ = 2 * ((z / 2) ^^^ q.val) + ((z % 2) ^^^ 0) := nat_xor_two_mul _ _ _ _ (Nat.mod_lt z (by omega)) (by omega)
              _ = _ := by simp
          rw [h]; exact popcount_two_mul_add _ _ (Nat.mod_lt z (by omega))
        have hpop_o : popcount (z ^^^ (2 * q.val + 1)) = ((z % 2) ^^^ 1) + popcount ((z / 2) ^^^ q.val) := by
          have h : z ^^^ (2 * q.val + 1) = 2 * ((z / 2) ^^^ q.val) + ((z % 2) ^^^ 1) := by
            calc z ^^^ (2 * q.val + 1) = (2 * (z / 2) + z % 2) ^^^ (2 * q.val + 1) := by rw [← hz]
              _ = _ := nat_xor_two_mul _ _ _ _ (Nat.mod_lt z (by omega)) (by omega)
          rw [h]; exact popcount_two_mul_add _ _ (Nat.xor_lt_two_pow (n := 1) (Nat.mod_lt z (by omega)) (by omega))
        rw [he_div, he_mod, ho_div, ho_mod]
        simp only [↓reduceIte, show (1 : Nat) ≠ 0 by omega]
        by_cases hsub : (z / 2) &&& q.val = q.val
        · by_cases hm : z % 2 = 0
          · have h1 : z &&& (2 * q.val) = 2 * q.val := hsub_e.mpr hsub
            have h2 : ¬ (z &&& (2 * q.val + 1) = 2 * q.val + 1) := fun h => by have := (hsub_o.mp h).2; omega
            simp only [h1, h2, hsub, hm, ↓reduceIte, Int.add_zero, hpop_e, Nat.zero_add]
            rw [← hcontr_mul]
          · have hm1 : z % 2 = 1 := by omega
            have h1 : z &&& (2 * q.val) = 2 * q.val := hsub_e.mpr hsub
            have h2 : z &&& (2 * q.val + 1) = 2 * q.val + 1 := hsub_o.mpr ⟨hsub, hm1⟩
            simp only [h1, h2, hsub, hm1, ↓reduceIte, hpop_e, hpop_o, show (1 : Nat) ^^^ 1 = 0 by decide,
                       show (1 : Nat) ≠ 0 by omega, Nat.zero_add, signPow_add, signPow_one, Int.neg_one_mul]
            rw [← hcontr_mul (evalWord A.T0 A.T1 k q.val)]
            rw [Int.add_comm, Int.neg_mul, ← Int.mul_neg, ← Int.mul_add]
            congr 1
            rw [← Int.sub_eq_add_neg, ← contract_sub, ← matMul_sub_right]
        · have h1 : ¬ (z &&& (2 * q.val) = 2 * q.val) := fun h => hsub (hsub_e.mp h)
          have h2 : ¬ (z &&& (2 * q.val + 1) = 2 * q.val + 1) := fun h => hsub (hsub_o.mp h).1
          simp [h1, h2, hsub]
      change listSum (finList (2 ^ k)) _ = _
      rw [listSum_congr (fun q _ => hterm q)]
      have hstep := ih (z / 2) hz2 (fun i => sumFin d (fun j => (if z % 2 = 0 then A.T0 else matSub A.T1 A.T0) i j * β j))
      unfold mobiusDown at hstep
      change listSum (finList (2 ^ k)) _ = _ at hstep
      rw [hstep, ← hcontr_mul]
      rfl
  intro z hz
  exact hmat k z hz A.β

/-! ## Part 9: Reusable Collapse Mechanism I — Scaled-Dihedral Finite Certificate → Inverse-Gray Law -/

theorem matPow_zero {d : Nat} (M : Mat d) : matPow M 0 = matId d := rfl

theorem matPow_succ {d : Nat} (M : Mat d) (n : Nat) : matPow M (n + 1) = matMul (matPow M n) M := rfl

theorem matPow_one {d : Nat} (M : Mat d) : matPow M 1 = M := matMul_id_left M

theorem invGray_zero : invGray 0 = 0 := by simp [invGray]

theorem invGray_div2_step (n : Nat) :
    invGray n = 2 * invGray (n / 2) + ((invGray (n / 2) % 2) ^^^ (n % 2)) := by
  cases n with
  | zero => simp [invGray]
  | succ m => rw [invGray]

theorem grayCode_invGray (u : Nat) : grayCode (invGray u) = u := by
  induction u using Nat.strongRecOn with
  | ind u ih =>
    by_cases hu : u = 0
    · subst hu; simp [grayCode, invGray_zero]
    · have hlt : u / 2 < u := Nat.div_lt_self (Nat.pos_of_ne_zero hu) (by omega)
      rw [invGray_div2_step u]
      let g := invGray (u / 2)
      have hb : (g % 2) ^^^ (u % 2) < 2 := Nat.xor_lt_two_pow (n := 1) (Nat.mod_lt g (by omega)) (Nat.mod_lt u (by omega))
      unfold grayCode
      have hdiv : (2 * g + ((g % 2) ^^^ (u % 2))) / 2 = g := by omega
      rw [hdiv]
      have hg : g = 2 * (g / 2) + g % 2 := (Nat.div_add_mod g 2).symm
      calc (2 * g + ((g % 2) ^^^ (u % 2))) ^^^ g
          = (2 * g + ((g % 2) ^^^ (u % 2))) ^^^ (2 * (g / 2) + g % 2) := by rw [← hg]
        _ = 2 * (g ^^^ (g / 2)) + (((g % 2) ^^^ (u % 2)) ^^^ (g % 2)) := nat_xor_two_mul _ _ _ _ hb (Nat.mod_lt g (by omega))
        _ = 2 * (u / 2) + u % 2 := by
            congr 1
            · congr 1; exact ih (u / 2) hlt
            · rw [Nat.xor_comm (g % 2) (u % 2), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        _ = u := Nat.div_add_mod u 2

theorem invGray_grayCode (w : Nat) : invGray (grayCode w) = w := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
    by_cases hw : w = 0
    · subst hw; simp [grayCode, invGray_zero]
    · have hlt : w / 2 < w := Nat.div_lt_self (Nat.pos_of_ne_zero hw) (by omega)
      have hw2 : w = 2 * (w / 2) + w % 2 := (Nat.div_add_mod w 2).symm
      have hw4 : w / 2 = 2 * ((w / 2) / 2) + (w / 2) % 2 := (Nat.div_add_mod (w / 2) 2).symm
      have hgw : grayCode w = 2 * grayCode (w / 2) + ((w % 2) ^^^ ((w / 2) % 2)) := by
        unfold grayCode
        calc w ^^^ (w / 2) = (2 * (w / 2) + w % 2) ^^^ (2 * ((w / 2) / 2) + (w / 2) % 2) := by rw [← hw2, ← hw4]
          _ = _ := nat_xor_two_mul _ _ _ _ (Nat.mod_lt w (by omega)) (Nat.mod_lt (w / 2) (by omega))
      have hb : (w % 2) ^^^ ((w / 2) % 2) < 2 := Nat.xor_lt_two_pow (n := 1) (Nat.mod_lt w (by omega)) (Nat.mod_lt (w / 2) (by omega))
      rw [invGray_div2_step (grayCode w)]
      have hdiv : grayCode w / 2 = grayCode (w / 2) := by rw [hgw]; omega
      have hmod : grayCode w % 2 = (w % 2) ^^^ ((w / 2) % 2) := by rw [hgw]; omega
      rw [hdiv, hmod, ih (w / 2) hlt]
      have hbit : ((w / 2) % 2) ^^^ ((w % 2) ^^^ ((w / 2) % 2)) = w % 2 := by
        rw [Nat.xor_comm (w % 2), ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      rw [hbit]
      exact Nat.div_add_mod w 2

theorem invGray_lt_pow2 {k u : Nat} (hu : u < 2 ^ k) : invGray u < 2 ^ k := by
  induction k generalizing u with
  | zero =>
    have : u = 0 := by omega
    subst this; simp [invGray_zero]
  | succ k ih =>
    rw [invGray_div2_step u]
    have hu2 : u / 2 < 2 ^ k := by rw [Nat.pow_succ] at hu; omega
    have hg : invGray (u / 2) < 2 ^ k := ih hu2
    have hb : (invGray (u / 2) % 2) ^^^ (u % 2) < 2 :=
      Nat.xor_lt_two_pow (n := 1) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    rw [Nat.pow_succ]; omega

theorem popcount_le_width {k w : Nat} (hw : w < 2 ^ k) : popcount w ≤ k := by
  induction k generalizing w with
  | zero =>
    have : w = 0 := by omega
    subst this; simp [popcount_zero]
  | succ k ih =>
    rw [popcount_div2_step w]
    have hw2 : w / 2 < 2 ^ k := by rw [Nat.pow_succ] at hw; omega
    have := ih hw2
    omega

theorem popcount_ge_mod2 (w : Nat) : w % 2 ≤ popcount w := by
  rw [popcount_div2_step w]; omega

/-- **FINITE-TO-INFINITE SCALED-DIHEDRAL COLLAPSE THEOREM:**
    For ANY finite `d × d` scaled-dihedral certificate `cert`, EVERY `k`-bit transfer word
    `evalWord cert.A cert.S k u` (`u < 2^k`) collapses identically to:
      `c^(min (v - p) (k - v)) * signedPow A Abar (k - 2v + p) * S^p`
    where `v = popcount (invGray u)` and `p = invGray u % 2`! -/
theorem scaledDihedral_collapse {d : Nat} (cert : ScaledDihedralCert d) :
    ∀ (k u : Nat), u < 2 ^ k →
      let v := popcount (invGray u)
      let p := invGray u % 2
      let r0 := Nat.min (v - p) (k - v)
      let e : Int := (k : Int) - 2 * (v : Int) + (p : Int)
      evalWord cert.A cert.S k u =
      matScale (cert.c ^ r0) (matMul (signedPow cert.A cert.Abar e) (if p = 0 then matId d else cert.S)) := by
  intro k
  induction k with
  | zero =>
    intro u hu
    have hu0 : u = 0 := by omega
    subst hu0
    simp [evalWord, invGray_zero, popcount_zero, signedPow, matPow_zero, matMul_id_left]
    funext i j; unfold matScale; simp
  | succ k ih =>
    intro u hu
    have hu2 : u / 2 < 2 ^ k := by rw [Nat.pow_succ] at hu; omega
    have hih := ih (u / 2) hu2
    dsimp only at hih ⊢
    let g1 := invGray (u / 2)
    let v1 := popcount g1
    let p1 := g1 % 2
    have hv1_le : v1 ≤ k := popcount_le_width (invGray_lt_pow2 hu2)
    have hp1_le : p1 ≤ v1 := popcount_ge_mod2 g1
    have hp1_lt : p1 < 2 := Nat.mod_lt g1 (by omega)
    have hgu : invGray u = 2 * g1 + (p1 ^^^ (u % 2)) := invGray_div2_step u
    have hb_lt : p1 ^^^ (u % 2) < 2 := Nat.xor_lt_two_pow (n := 1) hp1_lt (Nat.mod_lt u (by omega))
    have hpu : invGray u % 2 = p1 ^^^ (u % 2) := by rw [hgu]; omega
    have hvu : popcount (invGray u) = (p1 ^^^ (u % 2)) + v1 := by rw [hgu, popcount_two_mul_add _ _ hb_lt]
    have hsp_mul_A : ∀ e : Int,
        matMul (signedPow cert.A cert.Abar e) cert.A =
        if e ≥ 0 then signedPow cert.A cert.Abar (e + 1)
        else matScale cert.c (signedPow cert.A cert.Abar (e + 1)) := by
      intro e
      unfold signedPow
      by_cases he : e ≥ 0
      · have he1 : e + 1 ≥ 0 := by omega
        have ht : (e + 1).toNat = e.toNat + 1 := by omega
        simp only [he, he1, ↓reduceIte, ht, matPow_succ]
      · have he_neg : (-e).toNat = (-(e + 1)).toNat + 1 := by omega
        simp only [he, ↓reduceIte, he_neg, matPow_succ]
        rw [← matMul_assoc, cert.hAbarA, matMul_scale_right, matMul_id_right]
        by_cases h0 : e + 1 ≥ 0
        · have heq : e = -1 := by omega
          subst heq
          simp [matPow_zero]
        · simp [h0]
    have hsp_mul_Abar : ∀ e : Int,
        matMul (signedPow cert.A cert.Abar e) cert.Abar =
        if e ≤ 0 then signedPow cert.A cert.Abar (e - 1)
        else matScale cert.c (signedPow cert.A cert.Abar (e - 1)) := by
      intro e
      unfold signedPow
      by_cases he : e ≤ 0
      · by_cases he0 : e = 0
        · subst he0
          have hnot : ¬ ((-1 : Int) ≥ 0) := by omega
          simp [matPow_zero, matPow_one, matMul_id_left]
        · have hnot1 : ¬ (e ≥ 0) := by omega
          have hnot2 : ¬ (e - 1 ≥ 0) := by omega
          have ht : (-(e - 1)).toNat = (-e).toNat + 1 := by omega
          simp only [he, hnot1, hnot2, ↓reduceIte, ht, matPow_succ]
      · have he_pos : e ≥ 0 := by omega
        have he1_ge : e - 1 ≥ 0 := by omega
        have ht : e.toNat = (e - 1).toNat + 1 := by omega
        simp only [he, he_pos, he1_ge, ↓reduceIte, ht, matPow_succ]
        rw [← matMul_assoc, cert.hAAbar, matMul_scale_right, matMul_id_right]
    rw [evalWord, hih, matMul_scale_left]
    rw [hvu, hpu]
    have hp1_cases : invGray (u / 2) % 2 = 0 ∨ invGray (u / 2) % 2 = 1 := by omega
    have hu_cases : u % 2 = 0 ∨ u % 2 = 1 := by omega
    dsimp only [v1, p1, g1] at hv1_le hp1_le ⊢
    rcases hp1_cases with hp0 | hp1 <;> rcases hu_cases with hm0 | hm1
    · simp only [hp0, hm0, ↓reduceIte, show (0 : Nat) ^^^ 0 = 0 by decide, Nat.zero_add,
                 matMul_id_right, Int.ofNat_zero, Int.add_zero, Nat.sub_zero]
      rw [hsp_mul_A]
      by_cases he : (k : Int) - 2 * (popcount (invGray (u / 2)) : Int) ≥ 0
      · have hmin : Nat.min (popcount (invGray (u / 2))) (k + 1 - popcount (invGray (u / 2))) =
                    Nat.min (popcount (invGray (u / 2))) (k - popcount (invGray (u / 2))) := by
          simp only [Nat.min_def]; split <;> split <;> omega
        have hexp : ((k + 1 : Nat) : Int) - 2 * (popcount (invGray (u / 2)) : Int) =
                    (k : Int) - 2 * (popcount (invGray (u / 2)) : Int) + 1 := by omega
        simp only [he, ↓reduceIte, hmin, hexp]
      · have hmin : Nat.min (popcount (invGray (u / 2))) (k + 1 - popcount (invGray (u / 2))) =
                    Nat.min (popcount (invGray (u / 2))) (k - popcount (invGray (u / 2))) + 1 := by
          simp only [Nat.min_def]; split <;> split <;> omega
        have hexp : ((k + 1 : Nat) : Int) - 2 * (popcount (invGray (u / 2)) : Int) =
                    (k : Int) - 2 * (popcount (invGray (u / 2)) : Int) + 1 := by omega
        simp only [he, ↓reduceIte, hmin, hexp, matScale_mul, Int.pow_succ]
    · simp only [hp0, hm1, show (1 : Nat) ≠ 0 by omega, ↓reduceIte, show (0 : Nat) ^^^ 1 = 1 by decide,
                 matMul_id_right, Nat.sub_zero, Int.ofNat_zero, Int.add_zero]
      have hmin : Nat.min (1 + popcount (invGray (u / 2)) - 1) (k + 1 - (1 + popcount (invGray (u / 2)))) =
                  Nat.min (popcount (invGray (u / 2))) (k - popcount (invGray (u / 2))) := by
        simp only [Nat.min_def]; split <;> split <;> omega
      have hexp : ((k + 1 : Nat) : Int) - 2 * ((1 + popcount (invGray (u / 2)) : Nat) : Int) + (1 : Nat) =
                  (k : Int) - 2 * (popcount (invGray (u / 2)) : Int) := by omega
      rw [hmin, hexp]
    · simp only [hp1, hm0, show (1 : Nat) ≠ 0 by omega, ↓reduceIte, show (1 : Nat) ^^^ 0 = 1 by decide]
      rw [← matMul_assoc, cert.hSA, matMul_assoc, hsp_mul_Abar]
      by_cases he : (k : Int) - 2 * (popcount (invGray (u / 2)) : Int) + (1 : Nat) ≤ 0
      · have hmin : Nat.min (1 + popcount (invGray (u / 2)) - 1) (k + 1 - (1 + popcount (invGray (u / 2)))) =
                    Nat.min (popcount (invGray (u / 2)) - 1) (k - popcount (invGray (u / 2))) := by
          simp only [Nat.min_def]; split <;> split <;> omega
        have hexp : ((k + 1 : Nat) : Int) - 2 * ((1 + popcount (invGray (u / 2)) : Nat) : Int) + (1 : Nat) =
                    (k : Int) - 2 * (popcount (invGray (u / 2)) : Int) + (1 : Nat) - 1 := by omega
        simp only [he, ↓reduceIte, hmin, hexp]
      · have hmin : Nat.min (1 + popcount (invGray (u / 2)) - 1) (k + 1 - (1 + popcount (invGray (u / 2)))) =
                    Nat.min (popcount (invGray (u / 2)) - 1) (k - popcount (invGray (u / 2))) + 1 := by
          simp only [Nat.min_def]; split <;> split <;> omega
        have hexp : ((k + 1 : Nat) : Int) - 2 * ((1 + popcount (invGray (u / 2)) : Nat) : Int) + (1 : Nat) =
                    (k : Int) - 2 * (popcount (invGray (u / 2)) : Int) + (1 : Nat) - 1 := by omega
        simp only [he, ↓reduceIte, hmin, hexp, matMul_scale_left, matScale_mul, Int.pow_succ]
    · simp only [hp1, hm1, show (1 : Nat) ≠ 0 by omega, ↓reduceIte, show (1 : Nat) ^^^ 1 = 0 by decide,
                 Nat.zero_add, Nat.sub_zero, Int.ofNat_zero, Int.add_zero]
      rw [← matMul_assoc, cert.hS2, matMul_scale_right, matMul_id_right, matScale_mul, matMul_id_right]
      have hmin : Nat.min (popcount (invGray (u / 2))) (k + 1 - popcount (invGray (u / 2))) =
                  Nat.min (popcount (invGray (u / 2)) - 1) (k - popcount (invGray (u / 2))) + 1 := by
        simp only [Nat.min_def]; split <;> split <;> omega
      have hexp : ((k + 1 : Nat) : Int) - 2 * (popcount (invGray (u / 2)) : Int) =
                  (k : Int) - 2 * (popcount (invGray (u / 2)) : Int) + (1 : Nat) := by omega
      rw [hmin, hexp, Int.pow_succ]

/-! ## Part 10: Concrete Novel Infinite Theorems — Binary-Runs & 2-Parameter Binary-Transition Kernels -/

theorem runs_zero : runs 0 = 0 := by simp [runs]

theorem runs_div2_step (n : Nat) :
    runs n = runs (n / 2) + (if n % 2 = 1 ∧ (n / 2) % 2 = 0 then 1 else 0) := by
  cases n with
  | zero => simp [runs]
  | succ m => rw [runs]

theorem runs_ge_mod2 (z : Nat) : z % 2 ≤ runs z := by
  induction z using Nat.strongRecOn with
  | ind z ih =>
    by_cases hz : z = 0
    · subst hz; simp [runs_zero]
    · rw [runs_div2_step z]
      have hlt : z / 2 < z := Nat.div_lt_self (Nat.pos_of_ne_zero hz) (by omega)
      have hih := ih (z / 2) hlt
      by_cases hm : z % 2 = 1 <;> by_cases hd : (z / 2) % 2 = 0 <;> simp [hm, hd] <;> omega

theorem transKernel_one (q : Int) (z : Nat) : transKernel q 1 z = runsKernel q z := by
  unfold transKernel runsKernel; simp [Int.one_pow]

theorem transAuto_correct (q s : Int) :
    ∀ (k z : Nat), z < 2 ^ k →
      evalWord (transAuto q s).T0 (transAuto q s).T1 k z ⟨0, by omega⟩ ⟨0, by omega⟩ =
        (if z % 2 = 0 then transKernel q s z else 0) ∧
      evalWord (transAuto q s).T0 (transAuto q s).T1 k z ⟨0, by omega⟩ ⟨1, by omega⟩ =
        (if z % 2 = 1 then transKernel q s z else 0) := by
  intro k
  induction k with
  | zero =>
    intro z hz
    have hz0 : z = 0 := by omega
    subst hz0
    simp [evalWord, matId, transKernel, runs_zero, falls]
  | succ k ih =>
    intro z hz
    have hz2 : z / 2 < 2 ^ k := by rw [Nat.pow_succ] at hz; omega
    rcases ih (z / 2) hz2 with ⟨h0, h1⟩
    rw [evalWord]
    have hruns := runs_div2_step z
    have hge := runs_ge_mod2 (z / 2)
    by_cases hzm : z % 2 = 0
    · simp only [hzm, ↓reduceIte, show (0 : Nat) ≠ 1 by omega]
      constructor
      · unfold matMul; rw [sumFin_two, h0, h1]
        dsimp only [transAuto]
        have hr : runs z = runs (z / 2) := by rw [hruns]; simp [hzm]
        by_cases hdm : (z / 2) % 2 = 0
        · simp [hdm, transKernel, falls, hr, hzm]
        · have hd1 : (z / 2) % 2 = 1 := by omega
          simp only [hd1, show (1 : Nat) ≠ 0 by omega, ↓reduceIte, Int.zero_mul, Int.zero_add]
          unfold transKernel falls
          have hf : runs (z / 2) - 0 = (runs (z / 2) - 1) + 1 := by omega
          rw [hr, hzm, hd1, hf, Int.pow_succ, Int.mul_assoc]
      · unfold matMul; rw [sumFin_two]; dsimp only [transAuto]; simp
    · have hz1 : z % 2 = 1 := by omega
      simp only [hz1, show (1 : Nat) ≠ 0 by omega, ↓reduceIte]
      constructor
      · unfold matMul; rw [sumFin_two]; dsimp only [transAuto]; simp
      · unfold matMul; rw [sumFin_two, h0, h1]
        dsimp only [transAuto]
        by_cases hdm : (z / 2) % 2 = 0
        · simp only [hdm, show (0 : Nat) ≠ 1 by omega, ↓reduceIte, Int.zero_mul, Int.add_zero]
          unfold transKernel falls
          have hr : runs z = runs (z / 2) + 1 := by rw [hruns]; simp [hz1, hdm]
          rw [hr, hz1, hdm, Int.pow_succ]
          have hsub0 : runs (z / 2) + 1 - 1 = runs (z / 2) - 0 := by omega
          rw [hsub0]
          calc q ^ runs (z / 2) * s ^ (runs (z / 2) - 0) * q
              = q ^ runs (z / 2) * (s ^ (runs (z / 2) - 0) * q) := Int.mul_assoc _ _ _
            _ = q ^ runs (z / 2) * (q * s ^ (runs (z / 2) - 0)) := by rw [Int.mul_comm _ q]
            _ = q ^ runs (z / 2) * q * s ^ (runs (z / 2) - 0) := (Int.mul_assoc _ _ _).symm
        · have hd1 : (z / 2) % 2 = 1 := by omega
          simp only [hd1, show (1 : Nat) ≠ 0 by omega, ↓reduceIte, Int.zero_mul, Int.zero_add, Int.mul_one]
          unfold transKernel falls
          have hr : runs z = runs (z / 2) := by rw [hruns]; simp [hz1, hdm]
          rw [hr, hz1, hd1]

theorem evalAuto_transAuto (q s : Int) (k z : Nat) (hz : z < 2 ^ k) :
    evalAuto (transAuto q s) k z = transKernel q s z := by
  unfold evalAuto contract
  rw [sumFin_two, sumFin_two, sumFin_two]
  rcases transAuto_correct q s k z hz with ⟨h0, h1⟩
  rw [h0, h1]
  dsimp only [transAuto]
  by_cases hm : z % 2 = 0
  · simp [hm]
  · have hm1 : z % 2 = 1 := by omega
    simp [hm1]

/-! ### Theorem 1: Exact Closed-Form Inverse-Gray `q`-Pell-Lucas Spectrum & Characteristic Polynomial -/

theorem runs_A_pow_row0 (q : Int) :
    ∀ m : Nat,
      matPow (transDihedralCert q 1).A m ⟨0, by omega⟩ ⟨0, by omega⟩ = pellQ q m ∧
      matPow (transDihedralCert q 1).A m ⟨0, by omega⟩ ⟨1, by omega⟩ = pellQ q (m + 1) - pellQ q m := by
  intro m
  induction m with
  | zero =>
    simp [matPow_zero, matId, pellQ]
  | succ m ih =>
    rcases ih with ⟨h0, h1⟩
    rw [matPow_succ]
    constructor
    · unfold matMul; rw [sumFin_two, h0, h1]
      dsimp only [transDihedralCert, matAdd, transAuto]; simp; omega
    · unfold matMul; rw [sumFin_two, h0, h1]
      dsimp only [transDihedralCert, matAdd, transAuto]; simp
      have hrec : pellQ q (m + 2) = 2 * pellQ q (m + 1) + (q - 1) * pellQ q m := rfl
      rw [hrec, Int.sub_mul, Int.one_mul, Int.mul_comm (pellQ q m) q]
      omega

theorem runs_Abar_pow_row0 (q : Int) :
    ∀ m : Nat,
      matPow (transDihedralCert q 1).Abar m ⟨0, by omega⟩ ⟨0, by omega⟩ = pellQ q m ∧
      matPow (transDihedralCert q 1).Abar m ⟨0, by omega⟩ ⟨1, by omega⟩ = -(pellQ q (m + 1) - pellQ q m) := by
  intro m
  induction m with
  | zero =>
    simp [matPow_zero, matId, pellQ]
  | succ m ih =>
    rcases ih with ⟨h0, h1⟩
    rw [matPow_succ]
    constructor
    · unfold matMul; rw [sumFin_two, h0, h1]
      dsimp only [transDihedralCert]; simp; omega
    · unfold matMul; rw [sumFin_two, h0, h1]
      dsimp only [transDihedralCert]; simp
      have hrec : pellQ q (m + 2) = 2 * pellQ q (m + 1) + (q - 1) * pellQ q m := rfl
      rw [hrec, Int.sub_mul, Int.one_mul, Int.mul_neg, Int.mul_comm (pellQ q m) q]
      omega

theorem wht_runsKernel_closed_form (q : Int) (k u : Nat) (hu : u < 2 ^ k) :
    let v := popcount (invGray u)
    let r := Nat.min v (k + 1 - v)
    wht k (runsKernel q) u = (1 - q) ^ r * pellQ q (k + 1 - 2 * r) := by
  dsimp only
  have hwht_eq : wht k (runsKernel q) u = wht k (evalAuto (transAuto q 1) k) u := by
    unfold wht sumFin
    apply listSum_congr; intro z _
    rw [evalAuto_transAuto q 1 k z.val z.isLt, transKernel_one]
  rw [hwht_eq, wht_transfer_compiler (transAuto q 1) k u]
  unfold evalAuto whtAuto
  have hcol := scaledDihedral_collapse (transDihedralCert q 1) k u hu
  dsimp only [transDihedralCert] at hcol
  rw [hcol, contract_scale]
  have hv_le : popcount (invGray u) ≤ k := popcount_le_width (invGray_lt_pow2 hu)
  have hp_le : invGray u % 2 ≤ popcount (invGray u) := popcount_ge_mod2 (invGray u)
  have hp_cases : invGray u % 2 = 0 ∨ invGray u % 2 = 1 := by omega
  have hcontr_row0 : ∀ M : Mat 2, contract (transAuto q 1).α M (transAuto q 1).β =
      M ⟨0, by omega⟩ ⟨0, by omega⟩ + M ⟨0, by omega⟩ ⟨1, by omega⟩ := by
    intro M; unfold contract; rw [sumFin_two, sumFin_two, sumFin_two]; dsimp only [transAuto]; simp
  rw [hcontr_row0]
  have hS_right : ∀ M : Mat 2,
      matMul M (matSub (transAuto q 1).T0 (transAuto q 1).T1) ⟨0, by omega⟩ ⟨0, by omega⟩ +
      matMul M (matSub (transAuto q 1).T0 (transAuto q 1).T1) ⟨0, by omega⟩ ⟨1, by omega⟩ =
      (1 - q) * M ⟨0, by omega⟩ ⟨0, by omega⟩ := by
    intro M; unfold matMul; rw [sumFin_two, sumFin_two]
    dsimp only [matSub, transAuto]; simp only [↓reduceIte, show (0 : Nat) ≠ 1 by omega, show (1 : Nat) ≠ 0 by omega,
      Int.sub_zero, Int.zero_sub, Int.mul_one, Int.mul_neg, Int.sub_mul, Int.one_mul]
    rw [Int.mul_comm (M ⟨0, by omega⟩ ⟨0, by omega⟩) q]; omega
  rcases hp_cases with hp0 | hp1
  · simp only [hp0, ↓reduceIte, matMul_id_right, Int.ofNat_zero, Int.add_zero, Nat.sub_zero, Int.mul_one]
    unfold signedPow
    by_cases he : (k : Int) - 2 * (popcount (invGray u) : Int) ≥ 0
    · simp only [he, ↓reduceIte]
      have hrow := runs_A_pow_row0 q ((k : Int) - 2 * (popcount (invGray u) : Int)).toNat
      dsimp only [transDihedralCert] at hrow
      rw [hrow.1, hrow.2]
      have hr : Nat.min (popcount (invGray u)) (k + 1 - popcount (invGray u)) = popcount (invGray u) := by
        simp only [Nat.min_def]; split <;> omega
      have hmin : Nat.min (popcount (invGray u)) (k - popcount (invGray u)) = popcount (invGray u) := by
        simp only [Nat.min_def]; split <;> omega
      have hm : ((k : Int) - 2 * (popcount (invGray u) : Int)).toNat + 1 = k + 1 - 2 * popcount (invGray u) := by omega
      rw [hr, hmin, hm]; congr 1; omega
    · simp only [he, ↓reduceIte]
      have hrow := runs_Abar_pow_row0 q (-((k : Int) - 2 * (popcount (invGray u) : Int))).toNat
      dsimp only [transDihedralCert] at hrow
      rw [hrow.1, hrow.2]
      have hm_ge1 : (-((k : Int) - 2 * (popcount (invGray u) : Int))).toNat ≥ 1 := by omega
      have hrec : ∀ m : Nat, m ≥ 1 → pellQ q m + -(pellQ q (m + 1) - pellQ q m) = (1 - q) * pellQ q (m - 1) := by
        intro m hm
        cases m with
        | zero => omega
        | succ m' =>
          have hstep : pellQ q (m' + 2) = 2 * pellQ q (m' + 1) + (q - 1) * pellQ q m' := rfl
          rw [hstep]
          simp only [Int.sub_mul, Int.one_mul, Nat.add_sub_cancel]
          omega
      rw [hrec _ hm_ge1]
      have hr : Nat.min (popcount (invGray u)) (k + 1 - popcount (invGray u)) = k - popcount (invGray u) + 1 := by
        simp only [Nat.min_def]; split <;> omega
      have hmin : Nat.min (popcount (invGray u)) (k - popcount (invGray u)) = k - popcount (invGray u) := by
        simp only [Nat.min_def]; split <;> omega
      have hidx : (-((k : Int) - 2 * (popcount (invGray u) : Int))).toNat - 1 = k + 1 - 2 * (k - popcount (invGray u) + 1) := by omega
      rw [hr, hmin, hidx, ← Int.mul_assoc, Int.pow_succ]
  · simp only [hp1, show (1 : Nat) ≠ 0 by omega, ↓reduceIte, Int.mul_one]
    rw [hS_right]
    unfold signedPow
    by_cases he : (k : Int) - 2 * (popcount (invGray u) : Int) + (1 : Nat) ≥ 0
    · simp only [he, ↓reduceIte]
      have hrow := runs_A_pow_row0 q ((k : Int) - 2 * (popcount (invGray u) : Int) + (1 : Nat)).toNat
      dsimp only [transDihedralCert] at hrow
      rw [hrow.1]
      have hr : Nat.min (popcount (invGray u)) (k + 1 - popcount (invGray u)) = popcount (invGray u) := by
        simp only [Nat.min_def]; split <;> omega
      have hmin : Nat.min (popcount (invGray u) - 1) (k - popcount (invGray u)) = popcount (invGray u) - 1 := by
        simp only [Nat.min_def]; split <;> omega
      have hidx : ((k : Int) - 2 * (popcount (invGray u) : Int) + (1 : Nat)).toNat = k + 1 - 2 * popcount (invGray u) := by omega
      have hv_succ : Nat.succ (popcount (invGray u) - 1) = popcount (invGray u) := by omega
      rw [hr, hmin, hidx, ← Int.mul_assoc, ← Int.pow_succ, hv_succ]
    · simp only [he, ↓reduceIte]
      have hrow := runs_Abar_pow_row0 q (-((k : Int) - 2 * (popcount (invGray u) : Int) + (1 : Nat))).toNat
      dsimp only [transDihedralCert] at hrow
      rw [hrow.1]
      have hr : Nat.min (popcount (invGray u)) (k + 1 - popcount (invGray u)) = k - popcount (invGray u) + 1 := by
        simp only [Nat.min_def]; split <;> omega
      have hmin : Nat.min (popcount (invGray u) - 1) (k - popcount (invGray u)) = k - popcount (invGray u) := by
        simp only [Nat.min_def]; split <;> omega
      have hidx : (-((k : Int) - 2 * (popcount (invGray u) : Int) + (1 : Nat))).toNat = k + 1 - 2 * (k - popcount (invGray u) + 1) := by omega
      rw [hr, hmin, hidx, ← Int.mul_assoc, ← Int.pow_succ]

theorem charPoly_runs_xorConv (q : Int) (k : Nat) (lam : Int) :
    det (matSub (matScale lam (matId (2 ^ k))) (xorConvMat k (runsKernel q))) =
    prodFin (2 ^ k) (fun u =>
      let v := popcount (invGray u.val)
      let r := Nat.min v (k + 1 - v)
      lam - (1 - q) ^ r * pellQ q (k + 1 - 2 * r)) := by
  rw [charPoly_xorConv]
  unfold prodFin
  apply listProd_congr; intro u _
  rw [wht_runsKernel_closed_form q k u.val u.isLt]

theorem det_runs_xorConv (q : Int) (k : Nat) :
    det (xorConvMat k (runsKernel q)) =
    prodFin (2 ^ k) (fun u =>
      let v := popcount (invGray u.val)
      let r := Nat.min v (k + 1 - v)
      (1 - q) ^ r * pellQ q (k + 1 - 2 * r)) := by
  rw [det_xorConv]
  unfold prodFin
  apply listProd_congr; intro u _
  rw [wht_runsKernel_closed_form q k u.val u.isLt]

theorem runs_xorConv_neg_one_singular_odd (m : Nat) :
    det (xorConvMat (2 * m + 1) (runsKernel (-1))) = 0 := by
  rw [det_runs_xorConv]
  unfold prodFin
  have hpow_le : 2 ^ m ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hw_lt : 2 ^ m - 1 < 2 ^ (2 * m + 1) := by have := Nat.two_pow_pos m; omega
  have hu_lt : grayCode (2 ^ m - 1) < 2 ^ (2 * m + 1) := by
    unfold grayCode
    exact nat_xor_lt_pow2 hw_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hw_lt)
  let u₀ : Fin (2 ^ (2 * m + 1)) := ⟨grayCode (2 ^ m - 1), hu_lt⟩
  apply listProd_zero_of_mem (x := u₀) (mem_finList u₀)
  dsimp only [u₀]
  rw [invGray_grayCode]
  have hpop_ones : ∀ n : Nat, popcount (2 ^ n - 1) = n := by
    intro n
    induction n with
    | zero => simp [popcount_zero]
    | succ n ih =>
      have hpos := Nat.two_pow_pos n
      have heq : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by rw [Nat.pow_succ]; omega
      rw [heq, popcount_two_mul_add _ 1 (by omega), ih]; omega
  rw [hpop_ones m]
  have hr : Nat.min m (2 * m + 1 + 1 - m) = m := Nat.min_eq_left (by omega)
  have hidx : 2 * m + 1 + 1 - 2 * m = 2 := by omega
  rw [hr, hidx]
  have hp2 : pellQ (-1) 2 = 0 := by decide
  rw [hp2, Int.mul_zero]

/-! ### Theorem 2: Exact Closed-Form 2-Parameter Binary-Transition AND-Lattice Determinant & Unimodularity Law -/

theorem oddTrail_zero (m : Nat) : oddTrail m 0 = false := by
  cases m <;> rfl

theorem mobiusRay_snd_eq_oddTrail (q s : Int) (k z : Nat) :
    (mobiusRay q s k z).2 = oddTrail k z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    simp only [mobiusRay, oddTrail]
    rw [ih (z / 2)]
    split <;> cases oddTrail k (z / 2) <;> rfl

theorem transMobius_row0_collapse (q s : Int) :
    ∀ (k z : Nat),
      let M0 := (mobiusDownAuto (transAuto q s)).T0
      let M1 := (mobiusDownAuto (transAuto q s)).T1
      let st := mobiusRay q s k z
      evalWord M0 M1 k z ⟨0, by omega⟩ ⟨0, by omega⟩ = (if st.2 then -st.1 else st.1) ∧
      evalWord M0 M1 k z ⟨0, by omega⟩ ⟨1, by omega⟩ = (if st.2 then st.1 * q else 0) := by
  intro k
  induction k with
  | zero =>
    intro z; simp [evalWord, matId, mobiusRay]
  | succ k ih =>
    intro z
    rcases ih (z / 2) with ⟨h0, h1⟩
    dsimp only at h0 h1 ⊢
    rw [evalWord]
    simp only [mobiusRay]
    by_cases hm : z % 2 = 0
    · simp only [hm, ↓reduceIte]
      cases hst : (mobiusRay q s k (z / 2)).2 <;> rw [hst] at h0 h1
      · simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1 ⊢
        constructor <;> (unfold matMul; rw [sumFin_two, h0, h1]; dsimp only [mobiusDownAuto, transAuto]; simp)
      · simp only [↓reduceIte] at h0 h1 ⊢
        constructor
        · unfold matMul; rw [sumFin_two, h0, h1]; dsimp only [mobiusDownAuto, transAuto]; simp
          rw [Int.mul_sub, Int.mul_one, Int.mul_assoc]; omega
        · unfold matMul; rw [sumFin_two, h0, h1]; dsimp only [mobiusDownAuto, transAuto]; simp
    · simp only [hm, ↓reduceIte]
      cases hst : (mobiusRay q s k (z / 2)).2 <;> rw [hst] at h0 h1
      · simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1 ⊢
        constructor <;> (unfold matMul; rw [sumFin_two, h0, h1]; dsimp only [mobiusDownAuto, matSub, transAuto]; simp)
      · simp only [↓reduceIte] at h0 h1 ⊢
        constructor
        · unfold matMul; rw [sumFin_two, h0, h1]; dsimp only [mobiusDownAuto, matSub, transAuto]; simp
          rw [Int.mul_sub, Int.mul_one, Int.mul_assoc, Int.mul_neg, Int.mul_neg]; omega
        · unfold matMul; rw [sumFin_two, h0, h1]; dsimp only [mobiusDownAuto, matSub, transAuto]; simp
          rw [Int.neg_mul, Int.add_comm]; omega

theorem mobiusDown_transKernel_eq (q s : Int) (k z : Nat) (hz : z < 2 ^ k) :
    mobiusDown k (transKernel q s) z =
    (mobiusRay q s k z).1 * (if oddTrail k z then q - 1 else 1) := by
  have h1 : mobiusDown k (transKernel q s) z = mobiusDown k (evalAuto (transAuto q s) k) z := by
    unfold mobiusDown sumFin
    apply listSum_congr; intro w _
    split
    · rw [evalAuto_transAuto q s k w.val w.isLt]
    · rfl
  rw [h1, mobiusDown_transfer_compiler (transAuto q s) k z hz]
  unfold evalAuto contract
  rw [sumFin_two, sumFin_two, sumFin_two]
  rcases transMobius_row0_collapse q s k z with ⟨r0, r1⟩
  rw [r0, r1, mobiusRay_snd_eq_oddTrail]
  dsimp only [mobiusDownAuto, transAuto]
  cases oddTrail k z
  · simp
  · simp [Int.mul_sub]; omega

theorem jacobsthal_le_pow2 (k : Nat) : jacobsthal k ≤ 2 ^ k := by
  induction k with
  | zero => simp [jacobsthal]
  | succ k ih =>
    unfold jacobsthal
    rw [Nat.pow_succ]; omega

theorem int_natCast_pow2 (k : Nat) : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Int.pow_succ, ← ih]
    omega

theorem jacobsthal_closed_form (k : Nat) :
    3 * (jacobsthal k : Int) + signPow k = (2 : Int) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold jacobsthal
    have hle := jacobsthal_le_pow2 k
    have hcast : ((2 ^ k - jacobsthal k : Nat) : Int) = ((2 ^ k : Nat) : Int) - (jacobsthal k : Int) := by omega
    have hsp : signPow (k + 1) = -signPow k := by
      rw [signPow_add, signPow_one]; omega
    rw [hcast, int_natCast_pow2, hsp, Int.pow_succ]
    omega

theorem jacobsthal_odd (k : Nat) (hk : k ≥ 1) : jacobsthal k % 2 = 1 := by
  have hc := jacobsthal_closed_form k
  rw [← int_natCast_pow2] at hc
  have heven : (2 ^ k : Nat) % 2 = 0 := by
    cases k with
    | zero => omega
    | succ m => rw [Nat.pow_succ]; omega
  unfold signPow at hc
  split at hc <;> omega

theorem countOddTrail_eq_jacobsthal (k : Nat) : countOddTrail k = jacobsthal k := by
  have hcast : ∀ n : Nat, (countOddTrail n : Int) = sumFin (2 ^ n) (fun z => if oddTrail n z.val then 1 else 0) := by
    intro n
    unfold countOddTrail sumFin listSum
    induction (finList (2 ^ n)) with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.foldr_cons, Int.natCast_add, ih]
      cases oddTrail n x.val <;> simp
  suffices h : (countOddTrail k : Int) = (jacobsthal k : Int) by omega
  induction k with
  | zero =>
    rw [hcast 0]; rfl
  | succ k ih =>
    rw [hcast (k + 1), sumFin_pow2_succ]
    have hterm : ∀ q : Fin (2 ^ k),
        (if oddTrail (k + 1) (finEven q).val then (1 : Int) else 0) +
        (if oddTrail (k + 1) (finOdd q).val then (1 : Int) else 0) =
        1 - (if oddTrail k q.val then (1 : Int) else 0) := by
      intro q
      dsimp only [finEven, finOdd, oddTrail]
      have he_mod : (2 * q.val) % 2 = 0 := by omega
      have ho_mod : (2 * q.val + 1) % 2 = 1 := by omega
      have ho_div : (2 * q.val + 1) / 2 = q.val := by omega
      simp only [he_mod, ho_mod, ho_div, ↓reduceIte, show (1 : Nat) ≠ 0 by omega]
      cases oddTrail k q.val <;> simp
    unfold sumFin
    rw [listSum_congr (fun q _ => hterm q)]
    have hsub : listSum (finList (2 ^ k)) (fun q => (1 : Int) - (if oddTrail k q.val then 1 else 0)) =
                listSum (finList (2 ^ k)) (fun _ => 1) - listSum (finList (2 ^ k)) (fun q => if oddTrail k q.val then 1 else 0) := by
      have h1 : ∀ q : Fin (2 ^ k), (1 : Int) - (if oddTrail k q.val then 1 else 0) =
          1 + -(if oddTrail k q.val then 1 else 0) := fun _ => by omega
      rw [listSum_congr (fun q _ => h1 q), listSum_add, listSum_neg]; omega
    rw [hsub]
    have hones : ∀ l : List (Fin (2 ^ k)), listSum l (fun _ => 1) = (l.length : Int) := by
      intro l; induction l with
      | nil => rfl
      | cons _ xs ihl => simp [listSum_cons, ihl]; omega
    rw [hones, length_finList]
    have hih_eq : listSum (finList (2 ^ k)) (fun q => if oddTrail k q.val then 1 else 0) = (jacobsthal k : Int) := by
      rw [← ih, hcast k]; rfl
    rw [hih_eq]
    have hj_succ : jacobsthal (k + 1) = 2 ^ k - jacobsthal k := rfl
    rw [hj_succ]
    have hle := jacobsthal_le_pow2 k
    omega

theorem transExp_closed_form (k : Nat) :
    9 * (transExp k : Int) = (3 * (k : Int) - 2) * (2 : Int) ^ k + 2 * signPow k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold transExp
    have hj := jacobsthal_closed_form k
    have hsp : signPow (k + 1) = -signPow k := by rw [signPow_add, signPow_one]; omega
    have hcast : ((2 * transExp k + 2 * jacobsthal k : Nat) : Int) =
                 2 * (transExp k : Int) + 2 * (jacobsthal k : Int) := by omega
    rw [hcast, hsp, Int.pow_succ]
    have h9 : 9 * (2 * (transExp k : Int) + 2 * (jacobsthal k : Int)) =
              2 * (9 * (transExp k : Int)) + 6 * (3 * (jacobsthal k : Int)) := by omega
    rw [h9, ih]
    have h3j : 3 * (jacobsthal k : Int) = (2 : Int) ^ k - signPow k := by omega
    rw [h3j]
    have hmul : (3 * ((k + 1 : Nat) : Int) - 2) * ((2 : Int) ^ k * 2) =
                2 * ((3 * (k : Int) - 2) * (2 : Int) ^ k) + 6 * (2 : Int) ^ k := by
      have hk1 : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      rw [hk1]
      calc (3 * ((k : Int) + 1) - 2) * ((2 : Int) ^ k * 2)
          = ((3 * (k : Int) - 2) + 3) * (2 * (2 : Int) ^ k) := by rw [Int.mul_comm ((2 : Int) ^ k) 2]; congr 1; omega
        _ = (3 * (k : Int) - 2) * (2 * (2 : Int) ^ k) + 3 * (2 * (2 : Int) ^ k) := Int.add_mul _ _ _
        _ = 2 * ((3 * (k : Int) - 2) * (2 : Int) ^ k) + 6 * (2 : Int) ^ k := by
              rw [← Int.mul_assoc, Int.mul_comm (3 * (k : Int) - 2) 2, Int.mul_assoc]; omega
    rw [hmul]; omega

theorem runsExp_closed_form (k : Nat) :
    9 * ((transExp k + jacobsthal k : Nat) : Int) = (3 * (k : Int) + 1) * (2 : Int) ^ k - signPow k := by
  have he := transExp_closed_form k
  have hj := jacobsthal_closed_form k
  have hcast : ((transExp k + jacobsthal k : Nat) : Int) = (transExp k : Int) + (jacobsthal k : Int) := by omega
  rw [hcast]
  have h1 : 9 * ((transExp k : Int) + (jacobsthal k : Int)) = 9 * (transExp k : Int) + 3 * (3 * (jacobsthal k : Int)) := by omega
  rw [h1, he]
  have h3j : 3 * (jacobsthal k : Int) = (2 : Int) ^ k - signPow k := by omega
  rw [h3j]
  have hmul : (3 * (k : Int) + 1) * (2 : Int) ^ k = (3 * (k : Int) - 2) * (2 : Int) ^ k + 3 * (2 : Int) ^ k := by
    rw [← Int.add_mul]; congr 1; omega
  rw [hmul]; omega

theorem prod_if_oddTrail (k : Nat) (a : Int) :
    prodFin (2 ^ k) (fun z => if oddTrail k z.val then a else 1) = a ^ jacobsthal k := by
  rw [← countOddTrail_eq_jacobsthal]
  unfold prodFin countOddTrail listProd
  induction (finList (2 ^ k)) with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons, ih]
    cases oddTrail k x.val
    · simp
    · simp [Int.pow_add, Int.pow_one]

theorem prod_mobiusRay_scale (q s : Int) :
    ∀ k : Nat,
      prodFin (2 ^ k) (fun z => (mobiusRay q s k z.val).1) =
      (if k ≤ 1 then 1 else -1) * (q * s - 1) ^ (transExp k) := by
  intro k
  induction k with
  | zero =>
    unfold prodFin
    rw [show finList (2 ^ 0) = [⟨0, by omega⟩] by rfl]
    simp [listProd, mobiusRay, transExp]
  | succ k ih =>
    rw [prodFin_pow2_succ]
    have hpair : ∀ r : Fin (2 ^ k),
        (mobiusRay q s (k + 1) (finEven r).val).1 * (mobiusRay q s (k + 1) (finOdd r).val).1 =
        ((mobiusRay q s k r.val).1 * (mobiusRay q s k r.val).1) *
        (if oddTrail k r.val then -((q * s - 1) ^ 2) else 1) := by
      intro r
      dsimp only [finEven, finOdd, mobiusRay]
      have he_mod : (2 * r.val) % 2 = 0 := by omega
      have he_div : (2 * r.val) / 2 = r.val := by omega
      have ho_mod : (2 * r.val + 1) % 2 = 1 := by omega
      have ho_div : (2 * r.val + 1) / 2 = r.val := by omega
      rw [he_mod, he_div, ho_mod, ho_div, mobiusRay_snd_eq_oddTrail]
      cases oddTrail k r.val
      · simp
      · simp only [↓reduceIte, show (1 : Nat) ≠ 0 by omega]
        let c := (mobiusRay q s k r.val).1
        let t := q * s - 1
        have hneg : 1 - q * s = -t := by omega
        rw [hneg]
        calc c * t * (c * -t) = (c * c) * (t * -t) := by
              rw [Int.mul_assoc, ← Int.mul_assoc t c (-t), Int.mul_comm t c, Int.mul_assoc c t (-t), ← Int.mul_assoc]
          _ = (c * c) * -(t ^ 2) := by
              congr 1; rw [Int.mul_neg, Int.pow_succ, Int.pow_one]
    unfold prodFin
    rw [listProd_congr (fun r _ => hpair r), listProd_mul, listProd_mul]
    have hih : listProd (finList (2 ^ k)) (fun r => (mobiusRay q s k r.val).1) =
               (if k ≤ 1 then 1 else -1) * (q * s - 1) ^ transExp k := ih
    rw [hih]
    have hprod_odd : listProd (finList (2 ^ k)) (fun r => if oddTrail k r.val then -((q * s - 1) ^ 2) else 1) =
                     (-((q * s - 1) ^ 2)) ^ jacobsthal k := prod_if_oddTrail k (-((q * s - 1) ^ 2))
    rw [hprod_odd]
    let t := q * s - 1
    have hsq_sign : (if k ≤ 1 then (1 : Int) else -1) * (if k ≤ 1 then 1 else -1) = 1 := by
      split <;> rfl
    have hsq_left : ((if k ≤ 1 then (1 : Int) else -1) * t ^ transExp k) *
                    ((if k ≤ 1 then (1 : Int) else -1) * t ^ transExp k) = t ^ (2 * transExp k) := by
      calc ((if k ≤ 1 then (1 : Int) else -1) * t ^ transExp k) * ((if k ≤ 1 then (1 : Int) else -1) * t ^ transExp k)
          = ((if k ≤ 1 then (1 : Int) else -1) * (if k ≤ 1 then 1 else -1)) * (t ^ transExp k * t ^ transExp k) := by
              rw [Int.mul_assoc, ← Int.mul_assoc (t ^ transExp k), Int.mul_comm (t ^ transExp k), Int.mul_assoc, ← Int.mul_assoc]
        _ = 1 * t ^ (transExp k + transExp k) := by rw [hsq_sign, ← Int.pow_add]
        _ = t ^ (2 * transExp k) := by rw [Int.one_mul, Nat.two_mul]
    rw [hsq_left]
    have hneg_pow : (-(t ^ 2)) ^ jacobsthal k = signPow (jacobsthal k) * t ^ (2 * jacobsthal k) := by
      have haux : ∀ n : Nat, (-(t ^ 2)) ^ n = signPow n * t ^ (2 * n) := by
        intro n; induction n with
        | zero => simp [signPow_zero]
        | succ n ihn =>
          rw [Int.pow_succ, ihn]
          have hsp : signPow (n + 1) = -signPow n := by rw [signPow_add, signPow_one]; omega
          have hexp : 2 * (n + 1) = 2 * n + 2 := by omega
          rw [hsp, hexp, Int.pow_add, Int.mul_neg, Int.neg_mul, ← Int.mul_assoc]
      exact haux (jacobsthal k)
    rw [hneg_pow]
    have hte_succ : transExp (k + 1) = 2 * transExp k + 2 * jacobsthal k := rfl
    rw [hte_succ, Int.pow_add]
    have hre : t ^ (2 * transExp k) * (signPow (jacobsthal k) * t ^ (2 * jacobsthal k)) =
               signPow (jacobsthal k) * (t ^ (2 * transExp k) * t ^ (2 * jacobsthal k)) := by
      rw [← Int.mul_assoc, Int.mul_comm (t ^ (2 * transExp k)) (signPow (jacobsthal k)), Int.mul_assoc]
    rw [hre]
    congr 1
    cases k with
    | zero => simp [jacobsthal, signPow_zero]
    | succ m =>
      have hodd := jacobsthal_odd (m + 1) (by omega)
      have hsp : signPow (jacobsthal (m + 1)) = -1 := by unfold signPow; simp [hodd]
      rw [hsp]
      have hnot : ¬ (m + 1 + 1 ≤ 1) := by omega
      simp [hnot]

theorem det_trans_andLattice (q s : Int) (k : Nat) (hk : k ≥ 2) :
    det (andLatticeMat k (transKernel q s)) =
    -((q * s - 1) ^ (transExp k) * (q - 1) ^ (jacobsthal k)) := by
  rw [det_andLattice]
  unfold prodFin
  rw [listProd_congr (fun z _ => mobiusDown_transKernel_eq q s k z.val z.isLt)]
  rw [listProd_mul]
  have h1 := prod_mobiusRay_scale q s k
  have h2 := prod_if_oddTrail k (q - 1)
  unfold prodFin at h1 h2
  rw [h1, h2]
  have hnot : ¬ (k ≤ 1) := by omega
  simp only [hnot, ↓reduceIte, Int.neg_mul, Int.one_mul]

theorem det_runs_andLattice (q : Int) (k : Nat) (hk : k ≥ 2) :
    det (andLatticeMat k (runsKernel q)) =
    -((q - 1) ^ (transExp k + jacobsthal k)) := by
  have heq : andLatticeMat k (runsKernel q) = andLatticeMat k (transKernel q 1) := by
    funext x y; unfold andLatticeMat; rw [transKernel_one]
  rw [heq, det_trans_andLattice q 1 k hk, Int.mul_one, ← Int.pow_add]

theorem det_two_runs_andLattice_unimodular (k : Nat) (hk : k ≥ 2) :
    det (andLatticeMat k (runsKernel 2)) = -1 := by
  rw [det_runs_andLattice 2 k hk, show (2 : Int) - 1 = 1 from rfl, Int.one_pow]

theorem runs_andLattice_never_posdef (q : Int) (k : Nat) (hk : k ≥ 2) :
    ∃ v : Fin (2 ^ k) → Int, (∃ i, v i ≠ 0) ∧ quadForm (andLatticeMat k (runsKernel q)) v ≤ 0 := by
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  have h1_lt : 1 < 2 ^ k := by omega
  have h3_lt : 3 < 2 ^ k := by omega
  have heq : andLatticeMat k (runsKernel q) = andLatticeMat k (transKernel q 1) := by
    funext x y; unfold andLatticeMat; rw [transKernel_one]
  have hray_zero : ∀ m : Nat, mobiusRay q 1 m 0 = (1, false) := by
    intro m; induction m with
    | zero => rfl
    | succ m ihm => simp [mobiusRay, ihm]
  have hm1 : mobiusDown k (transKernel q 1) 1 = q - 1 := by
    rw [mobiusDown_transKernel_eq q 1 k 1 h1_lt]
    cases k with
    | zero => omega
    | succ m =>
      simp [mobiusRay, oddTrail, hray_zero, oddTrail_zero]
  have hm3 : mobiusDown k (transKernel q 1) 3 = 1 - q := by
    rw [mobiusDown_transKernel_eq q 1 k 3 h3_lt]
    rcases Nat.exists_eq_add_of_le hk with ⟨m, rfl⟩
    have hm_eq : 2 + m = (m + 1) + 1 := by omega
    rw [hm_eq]
    simp [mobiusRay, oddTrail, hray_zero, oddTrail_zero]
  by_cases hq : q ≤ 1
  · let z₁ : Fin (2 ^ k) := ⟨1, h1_lt⟩
    refine ⟨fun x => mobiusMat k z₁ x, ⟨z₁, ?_⟩, ?_⟩
    · simp [mobiusMat, popcount_zero, signPow_zero]
    · rw [heq, andLattice_quadForm_mobius_witness, hm1]; omega
  · let z₃ : Fin (2 ^ k) := ⟨3, h3_lt⟩
    refine ⟨fun x => mobiusMat k z₃ x, ⟨z₃, ?_⟩, ?_⟩
    · simp [mobiusMat, popcount_zero, signPow_zero]
    · rw [heq, andLattice_quadForm_mobius_witness, hm3]; omega

/-! ## Part 11: Non-Vacuity Witnesses & Kernel-Checked Sharpness Counterexamples -/

theorem popcount_0 : popcount 0 = 0 := popcount_zero

theorem popcount_1 : popcount 1 = 1 := by rw [popcount_div2_step]; simp [popcount_zero]

theorem popcount_2 : popcount 2 = 1 := by rw [popcount_div2_step]; simp [popcount_1]

theorem popcount_3 : popcount 3 = 2 := by rw [popcount_div2_step]; simp [popcount_1]

theorem popcount_4 : popcount 4 = 1 := by rw [popcount_div2_step]; simp [popcount_2]

theorem popcount_5 : popcount 5 = 2 := by rw [popcount_div2_step]; simp [popcount_2]

theorem popcount_6 : popcount 6 = 2 := by rw [popcount_div2_step]; simp [popcount_3]

theorem popcount_7 : popcount 7 = 3 := by rw [popcount_div2_step]; simp [popcount_3]

theorem invGray_0 : invGray 0 = 0 := invGray_zero

theorem invGray_1 : invGray 1 = 1 := by rw [invGray_div2_step]; simp [invGray_zero]

theorem invGray_2 : invGray 2 = 3 := by rw [invGray_div2_step]; simp [invGray_1]

theorem invGray_3 : invGray 3 = 2 := by rw [invGray_div2_step]; simp [invGray_1]

theorem invGray_4 : invGray 4 = 7 := by rw [invGray_div2_step]; simp [invGray_2]

theorem invGray_5 : invGray 5 = 6 := by rw [invGray_div2_step]; simp [invGray_2]

theorem invGray_6 : invGray 6 = 4 := by rw [invGray_div2_step]; simp [invGray_3]

theorem invGray_7 : invGray 7 = 5 := by rw [invGray_div2_step]; simp [invGray_3]

theorem runs_0 : runs 0 = 0 := runs_zero

theorem runs_1 : runs 1 = 1 := by rw [runs_div2_step]; simp [runs_zero]

theorem runs_2 : runs 2 = 1 := by rw [runs_div2_step]; simp [runs_1]

theorem runs_3 : runs 3 = 1 := by rw [runs_div2_step]; simp [runs_1]

theorem runs_4 : runs 4 = 1 := by rw [runs_div2_step]; simp [runs_2]

theorem runs_5 : runs 5 = 2 := by rw [runs_div2_step]; simp [runs_2]

theorem runs_6 : runs 6 = 1 := by rw [runs_div2_step]; simp [runs_3]

theorem runs_7 : runs 7 = 1 := by rw [runs_div2_step]; simp [runs_3]

theorem finList_two : finList 2 = [⟨0, by omega⟩, ⟨1, by omega⟩] := rfl

theorem finList_eight : finList 8 =
    [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩,
     ⟨4, by omega⟩, ⟨5, by omega⟩, ⟨6, by omega⟩, ⟨7, by omega⟩] := rfl

theorem witness_k1_q2_xor : det (xorConvMat 1 (runsKernel 2)) = -3 := by
  rw [det_runs_xorConv]
  unfold prodFin listProd
  rw [show 2 ^ 1 = 2 from rfl, finList_two]
  simp [invGray_0, invGray_1, popcount_0, popcount_1, pellQ]

theorem witness_k1_q2_and : det (andLatticeMat 1 (runsKernel 2)) = 1 := by
  rw [det_andLattice]
  unfold prodFin listProd mobiusDown sumFin listSum runsKernel
  rw [show 2 ^ 1 = 2 from rfl, finList_two]
  simp [runs_0, runs_1, popcount_0, popcount_1, signPow]

theorem sharpness_k1_q2_posdef :
    ∀ v : Fin (2 ^ 1) → Int, (∃ i, v i ≠ 0) → quadForm (andLatticeMat 1 (runsKernel 2)) v > 0 := by
  intro v ⟨i, hi⟩
  rw [andLattice_quadForm]
  rw [sumFin_two, sumFin_two, sumFin_two]
  have hm0 : mobiusDown 1 (runsKernel 2) 0 = 1 := by
    unfold mobiusDown sumFin listSum runsKernel
    rw [show 2 ^ 1 = 2 from rfl, finList_two]
    simp [runs_0, popcount_0, signPow]
  have hm1 : mobiusDown 1 (runsKernel 2) 1 = 1 := by
    unfold mobiusDown sumFin listSum runsKernel
    rw [show 2 ^ 1 = 2 from rfl, finList_two]
    simp [runs_0, runs_1, popcount_0, popcount_1, signPow]
  have hz00 : zetaMat 1 ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by decide
  have hz10 : zetaMat 1 ⟨1, by omega⟩ ⟨0, by omega⟩ = 1 := by decide
  have hz01 : zetaMat 1 ⟨0, by omega⟩ ⟨1, by omega⟩ = 0 := by decide
  have hz11 : zetaMat 1 ⟨1, by omega⟩ ⟨1, by omega⟩ = 1 := by decide
  change mobiusDown 1 (runsKernel 2) 0 * (zetaMat 1 ⟨0, by omega⟩ ⟨0, by omega⟩ * v ⟨0, by omega⟩ + zetaMat 1 ⟨1, by omega⟩ ⟨0, by omega⟩ * v ⟨1, by omega⟩) *
        (zetaMat 1 ⟨0, by omega⟩ ⟨0, by omega⟩ * v ⟨0, by omega⟩ + zetaMat 1 ⟨1, by omega⟩ ⟨0, by omega⟩ * v ⟨1, by omega⟩) +
      mobiusDown 1 (runsKernel 2) 1 * (zetaMat 1 ⟨0, by omega⟩ ⟨1, by omega⟩ * v ⟨0, by omega⟩ + zetaMat 1 ⟨1, by omega⟩ ⟨1, by omega⟩ * v ⟨1, by omega⟩) *
        (zetaMat 1 ⟨0, by omega⟩ ⟨1, by omega⟩ * v ⟨0, by omega⟩ + zetaMat 1 ⟨1, by omega⟩ ⟨1, by omega⟩ * v ⟨1, by omega⟩) > 0
  rw [hm0, hm1, hz00, hz10, hz01, hz11]
  let v0 := v ⟨0, by omega⟩
  let v1 := v ⟨1, by omega⟩
  have hnz : v0 ≠ 0 ∨ v1 ≠ 0 := by
    rcases fin2_cases i with rfl | rfl
    · left; exact hi
    · right; exact hi
  have hsq_nonneg : ∀ x : Int, x * x ≥ 0 := by
    intro x
    rcases Int.lt_trichotomy x 0 with hlt | rfl | hgt
    · exact Int.le_of_lt (Int.mul_pos_of_neg_of_neg hlt hlt)
    · decide
    · exact Int.le_of_lt (Int.mul_pos hgt hgt)
  have hsq1 : (v0 + v1) * (v0 + v1) ≥ 0 := hsq_nonneg (v0 + v1)
  have hsq2 : v1 * v1 ≥ 0 := hsq_nonneg v1
  have hpos : (v0 + v1) * (v0 + v1) + v1 * v1 > 0 := by
    by_cases hv1 : v1 = 0
    · have hv0 : v0 ≠ 0 := by rcases hnz with h | h; exact h; exact absurd hv1 h
      have h0sq : v0 * v0 > 0 := by
        rcases Int.lt_trichotomy v0 0 with hlt | heq | hgt
        · exact Int.mul_pos_of_neg_of_neg hlt hlt
        · exact absurd heq hv0
        · exact Int.mul_pos hgt hgt
      rw [hv1, Int.add_zero, Int.mul_zero, Int.add_zero]
      exact h0sq
    · have h1sq : v1 * v1 > 0 := by
        rcases Int.lt_trichotomy v1 0 with hlt | heq | hgt
        · exact Int.mul_pos_of_neg_of_neg hlt hlt
        · exact absurd heq hv1
        · exact Int.mul_pos hgt hgt
      omega
  have hsimpl : 1 * (1 * v0 + 1 * v1) * (1 * v0 + 1 * v1) + 1 * (0 * v0 + 1 * v1) * (0 * v0 + 1 * v1) =
                (v0 + v1) * (v0 + v1) + v1 * v1 := by
    simp only [Int.one_mul, Int.zero_mul, Int.zero_add]
  rw [hsimpl]; exact hpos

theorem sharpness_dihedral_trace_zero_necessary :
    popcount (invGray 2) = popcount (invGray 5) ∧
    wht 3 brokenKernel 2 ≠ wht 3 brokenKernel 5 := by
  constructor
  · simp [invGray_2, invGray_5, popcount_3, popcount_6]
  · unfold wht sumFin listSum brokenKernel
    rw [show 2 ^ 3 = 8 from rfl, finList_eight]
    dsimp only [List.foldr]
    rw [show (2 &&& 0 : Nat) = 0 by decide, show (2 &&& 1 : Nat) = 0 by decide,
        show (2 &&& 2 : Nat) = 2 by decide, show (2 &&& 3 : Nat) = 2 by decide,
        show (2 &&& 4 : Nat) = 0 by decide, show (2 &&& 5 : Nat) = 0 by decide,
        show (2 &&& 6 : Nat) = 2 by decide, show (2 &&& 7 : Nat) = 2 by decide,
        show (5 &&& 0 : Nat) = 0 by decide, show (5 &&& 1 : Nat) = 1 by decide,
        show (5 &&& 2 : Nat) = 0 by decide, show (5 &&& 3 : Nat) = 1 by decide,
        show (5 &&& 4 : Nat) = 4 by decide, show (5 &&& 5 : Nat) = 5 by decide,
        show (5 &&& 6 : Nat) = 4 by decide, show (5 &&& 7 : Nat) = 5 by decide]
    simp [popcount_0, popcount_1, popcount_2, popcount_3, popcount_4, popcount_5, popcount_6, popcount_7,
          runs_0, runs_1, runs_2, runs_3, runs_4, runs_5, runs_6, runs_7, signPow]

theorem witness_k2_q2_s3_and : det (andLatticeMat 2 (transKernel 2 3)) = -25 := by
  rw [det_trans_andLattice 2 3 2 (by omega)]; decide

theorem witness_k3_q2_xor : det (xorConvMat 3 (runsKernel 2)) = 1377 := by
  rw [det_runs_xorConv]
  unfold prodFin listProd
  rw [show 2 ^ 3 = 8 from rfl, finList_eight]
  dsimp only [List.foldr]
  simp [invGray_0, invGray_1, invGray_2, invGray_3, invGray_4, invGray_5, invGray_6, invGray_7,
        popcount_0, popcount_1, popcount_2, popcount_3, popcount_4, popcount_5, popcount_6, popcount_7, pellQ]

theorem witness_k3_q2_and : det (andLatticeMat 3 (runsKernel 2)) = -1 :=
  det_two_runs_andLattice_unimodular 3 (by omega)

theorem witness_nonempty_dihedral_cert : Nonempty (ScaledDihedralCert 2) :=
  ⟨transDihedralCert 2 1⟩

end SpecMat2
