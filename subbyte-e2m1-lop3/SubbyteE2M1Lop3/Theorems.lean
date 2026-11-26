/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubbyteE2M1Lop3.Defs

/-!
# Verified Proofs for Sub-Byte E2M1 & Minimal-`LOP3` Circuits (`subbyte-e2m1-lop3`)

All six headline theorems proved in pure Lean 4 `Init` (zero Mathlib, zero `sorry`,
zero `native_decide`), fast in both the Lean 4 kernel and Palomar `nanoda`.
-/

namespace SubbyteE2M1Lop3

/-! ## Section 1: General Cardinality, Pigeonhole & Bit-Flip Involution Helpers -/

private theorem countP_add_not {α : Type} (l : List α) (f : α → Bool) :
    l.countP f + l.countP (fun x => !f x) = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.countP_cons, List.length_cons]
    cases f a <;> simp <;> omega

private theorem weight_add_not {k : Nat} (f : BitVec k → Bool) :
    weight f + weight (fun x => !f x) = 2 ^ k := by
  unfold weight
  rw [countP_add_not, List.length_finRange]

private theorem countP_split {α : Type} (l : List α) (P Q : α → Bool) :
    l.countP P = l.countP (fun x => P x && Q x) + l.countP (fun x => P x && !Q x) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.countP_cons]
    cases P a <;> cases Q a <;> simp <;> omega

private theorem weight_split {k : Nat} (P Q : BitVec k → Bool) :
    weight P = weight (fun x => P x && Q x) + weight (fun x => P x && !Q x) :=
  countP_split (List.finRange (2 ^ k)) (fun i => P (BitVec.ofNat k i.val))
    (fun i => Q (BitVec.ofNat k i.val))

private theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] :
    ∀ (l₁ l₂ : List α), l₁.Nodup → (∀ x, x ∈ l₁ → x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l₂, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have ha : a ∈ l₂ := hsub a (List.mem_cons_self ..)
    have hsub' : ∀ x, x ∈ t → x ∈ l₂.erase a := by
      intro x hx
      have hne : x ≠ a := fun h => hnd.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (hsub x (List.mem_cons_of_mem a hx))
    have ih := length_le_of_nodup_subset t (l₂.erase a) hnd.2 hsub'
    have her : (l₂.erase a).length = l₂.length - 1 := List.length_erase_of_mem ha
    have hpos : 0 < l₂.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

private theorem le_weight_of_inj {m k : Nat} (f : BitVec k → Bool)
    (enc : Fin m → BitVec k) (hinj : ∀ a b, enc a = enc b → a = b)
    (hpred : ∀ a, f (enc a) = true) :
    m ≤ weight f := by
  unfold weight
  rw [List.countP_eq_length_filter]
  let idx : Fin m → Fin (2 ^ k) := fun a => ⟨(enc a).toNat, (enc a).isLt⟩
  have hidx_inj : ∀ a b, idx a = idx b → a = b := by
    intro a b hab
    apply hinj
    apply BitVec.eq_of_toNat_eq
    exact congrArg Fin.val hab
  have h1 : ((List.finRange m).map idx).Nodup :=
    (List.nodup_finRange m).map idx (fun _ _ hne heq => hne (hidx_inj _ _ heq))
  have hsub : ∀ i, i ∈ (List.finRange m).map idx →
      i ∈ (List.finRange (2 ^ k)).filter (fun j => f (BitVec.ofNat k j.val)) := by
    intro i hi
    rw [List.mem_map] at hi
    rcases hi with ⟨a, _, rfl⟩
    rw [List.mem_filter]
    refine ⟨List.mem_finRange _, ?_⟩
    simp only [idx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact hpred a
  have hle := length_le_of_nodup_subset _ _ h1 hsub
  rw [List.length_map, List.length_finRange] at hle
  exact hle

private theorem le_weight_of_exists {α : Type} {m k : Nat} (f : BitVec k → Bool)
    (g : BitVec k → α) (target : Fin m → α)
    (htinj : ∀ a b, target a = target b → a = b)
    (hsurj : ∀ a : Fin m, ∃ x : BitVec k, g x = target a)
    (himp : ∀ x a, g x = target a → f x = true) :
    m ≤ weight f := by
  let enc : Fin m → BitVec k := fun a => Classical.choose (hsurj a)
  have henc : ∀ a, g (enc a) = target a := fun a => Classical.choose_spec (hsurj a)
  apply le_weight_of_inj f enc
  · intro a b hab
    apply htinj
    rw [← henc a, ← henc b, hab]
  · intro a
    exact himp (enc a) a (henc a)

private def flipBit {k : Nat} (x : BitVec k) (j : Fin k) : BitVec k :=
  x ^^^ BitVec.ofNat k (1 <<< j.val)

private theorem flipBit_involutive {k : Nat} (x : BitVec k) (j : Fin k) :
    flipBit (flipBit x j) j = x := by
  unfold flipBit
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

private theorem getLsbD_one_shiftLeft {k : Nat} (j : Fin k) (i : Nat) :
    (BitVec.ofNat k (1 <<< j.val)).getLsbD i = decide (i = j.val) := by
  rw [BitVec.getLsbD_ofNat]
  by_cases hi : i = j.val
  · subst hi
    simp only [j.isLt, decide_true, Bool.true_and, Nat.testBit_shiftLeft, ge_iff_le,
      Nat.le_refl, Nat.sub_self, Nat.testBit_one_zero]
  · simp only [hi, decide_false, Nat.testBit_shiftLeft, ge_iff_le]
    by_cases hle : j.val ≤ i
    · have hne : i - j.val ≠ 0 := by omega
      simp only [hle, decide_true, Bool.true_and, Bool.and_eq_false_imp]
      intro _
      match hm : i - j.val with
      | 0 => exact absurd hm hne
      | _ + 1 => simp [Nat.testBit_succ]
    · simp [hle]

private theorem getLsbD_flipBit_self {k : Nat} (x : BitVec k) (j : Fin k) :
    (flipBit x j).getLsbD j.val = !x.getLsbD j.val := by
  unfold flipBit
  rw [BitVec.getLsbD_xor, getLsbD_one_shiftLeft]
  simp

private theorem getLsbD_flipBit_ne {k : Nat} (x : BitVec k) (j i : Fin k) (h : i ≠ j) :
    (flipBit x j).getLsbD i.val = x.getLsbD i.val := by
  unfold flipBit
  rw [BitVec.getLsbD_xor, getLsbD_one_shiftLeft]
  have hne : i.val ≠ j.val := fun he => h (Fin.ext he)
  simp [hne]

private theorem weight_le_of_flip_inv_dir {k : Nat} (f : BitVec k → Bool) (j : Fin k) (b : Bool)
    (hinv : ∀ x : BitVec k, f (flipBit x j) = f x) :
    weight (fun x => f x && (x.getLsbD j.val == b)) ≤
      weight (fun x => f x && (x.getLsbD j.val == !b)) := by
  unfold weight
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
  let fl : Fin (2 ^ k) → Fin (2 ^ k) := fun i =>
    ⟨(flipBit (BitVec.ofNat k i.val) j).toNat, (flipBit (BitVec.ofNat k i.val) j).isLt⟩
  have hfl_inj : ∀ i₁ i₂ : Fin (2 ^ k), fl i₁ = fl i₂ → i₁ = i₂ := by
    intro i₁ i₂ h
    have hbv : flipBit (BitVec.ofNat k i₁.val) j = flipBit (BitVec.ofNat k i₂.val) j :=
      BitVec.eq_of_toNat_eq (congrArg Fin.val h)
    have hbv2 : BitVec.ofNat k i₁.val = BitVec.ofNat k i₂.val := by
      have := congrArg (fun z => flipBit z j) hbv
      simpa [flipBit_involutive] using this
    have hnat := congrArg BitVec.toNat hbv2
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt i₁.isLt, Nat.mod_eq_of_lt i₂.isLt] at hnat
    exact Fin.ext hnat
  let l₁ := (List.finRange (2 ^ k)).filter (fun i =>
    f (BitVec.ofNat k i.val) && ((BitVec.ofNat k i.val).getLsbD j.val == b))
  let l₂ := (List.finRange (2 ^ k)).filter (fun i =>
    f (BitVec.ofNat k i.val) && ((BitVec.ofNat k i.val).getLsbD j.val == !b))
  have hnd : (l₁.map fl).Nodup :=
    ((List.nodup_finRange (2 ^ k)).filter _).map fl (fun _ _ hne heq => hne (hfl_inj _ _ heq))
  have hsub : ∀ z, z ∈ l₁.map fl → z ∈ l₂ := by
    intro z hz
    rw [List.mem_map] at hz
    rcases hz with ⟨i, hi, rfl⟩
    rw [List.mem_filter] at hi ⊢
    refine ⟨List.mem_finRange _, ?_⟩
    have hfi : f (BitVec.ofNat k i.val) = true := (Bool.and_eq_true _ _).mp hi.2 |>.1
    have hbi : ((BitVec.ofNat k i.val).getLsbD j.val == b) = true :=
      (Bool.and_eq_true _ _).mp hi.2 |>.2
    have hbi' : (BitVec.ofNat k i.val).getLsbD j.val = b := beq_iff_eq.mp hbi
    simp only [fl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [hinv, hfi, getLsbD_flipBit_self, hbi']
    simp
  have hle := length_le_of_nodup_subset (l₁.map fl) l₂ hnd hsub
  rw [List.length_map] at hle
  exact hle

private theorem weight_double_of_flip_inv {k : Nat} (f : BitVec k → Bool) (j : Fin k)
    (hinv : ∀ x : BitVec k, f (flipBit x j) = f x) :
    weight f = 2 * weight (fun x => f x && !x.getLsbD j.val) := by
  have h1 := weight_le_of_flip_inv_dir f j true hinv
  have h2 := weight_le_of_flip_inv_dir f j false hinv
  have htrue : (fun x : BitVec k => f x && (x.getLsbD j.val == true)) =
      (fun x => f x && x.getLsbD j.val) := by
    funext x; simp
  have hfalse : (fun x : BitVec k => f x && (x.getLsbD j.val == false)) =
      (fun x => f x && !x.getLsbD j.val) := by
    funext x; cases x.getLsbD j.val <;> rfl
  simp only [Bool.not_true, Bool.not_false, htrue, hfalse] at h1 h2
  have hsp := weight_split f (fun x => x.getLsbD j.val)
  omega

private theorem weight_mod_eight_of_three_flip_inv {k : Nat} (f : BitVec k → Bool)
    (j0 j1 j2 : Fin k) (h01 : j0 ≠ j1) (h02 : j0 ≠ j2) (h12 : j1 ≠ j2)
    (hinv0 : ∀ x, f (flipBit x j0) = f x)
    (hinv1 : ∀ x, f (flipBit x j1) = f x)
    (hinv2 : ∀ x, f (flipBit x j2) = f x) :
    weight f % 8 = 0 := by
  let f1 : BitVec k → Bool := fun x => f x && !x.getLsbD j0.val
  let f2 : BitVec k → Bool := fun x => f1 x && !x.getLsbD j1.val
  have hw0 : weight f = 2 * weight f1 := weight_double_of_flip_inv f j0 hinv0
  have hinv1' : ∀ x, f1 (flipBit x j1) = f1 x := by
    intro x
    simp only [f1, hinv1 x, getLsbD_flipBit_ne x j1 j0 h01]
  have hw1 : weight f1 = 2 * weight f2 := weight_double_of_flip_inv f1 j1 hinv1'
  have hinv2' : ∀ x, f2 (flipBit x j2) = f2 x := by
    intro x
    simp only [f2, f1, hinv2 x, getLsbD_flipBit_ne x j2 j0 h02, getLsbD_flipBit_ne x j2 j1 h12]
  have hw2 : weight f2 = 2 * weight (fun x => f2 x && !x.getLsbD j2.val) :=
    weight_double_of_flip_inv f2 j2 hinv2'
  omega

private theorem length_filter_ne_ge {α : Type} [DecidableEq α] (l : List α) (hnd : l.Nodup)
    (a : α) : l.length ≤ (l.filter (fun x => x != a)).length + 1 := by
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.length_cons, List.filter_cons]
    by_cases hxa : x = a
    · subst hxa
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      have hfilt : t.filter (fun y => y != x) = t := by
        apply List.filter_eq_self.mpr
        intro y hy
        exact bne_iff_ne.mpr (fun heq => hnd.1 (heq ▸ hy))
      rw [hfilt]
      omega
    · have hbne : (x != a) = true := bne_iff_ne.mpr hxa
      simp only [hbne, ↓reduceIte, List.length_cons]
      have := ih hnd.2
      omega

private theorem exists_three_outside2 (i0 i1 : Fin 5) :
    ∃ j0 j1 j2 : Fin 5,
      j0 ≠ j1 ∧ j0 ≠ j2 ∧ j1 ≠ j2 ∧
      j0 ≠ i0 ∧ j0 ≠ i1 ∧ j1 ≠ i0 ∧ j1 ≠ i1 ∧ j2 ≠ i0 ∧ j2 ≠ i1 := by
  let l0 := List.finRange 5
  let l1 := l0.filter (fun x => x != i0)
  let l2 := l1.filter (fun x => x != i1)
  have hnd0 : l0.Nodup := List.nodup_finRange 5
  have hnd1 : l1.Nodup := hnd0.filter _
  have hnd2 : l2.Nodup := hnd1.filter _
  have hlen1 : l0.length ≤ l1.length + 1 := length_filter_ne_ge l0 hnd0 i0
  have hlen2 : l1.length ≤ l2.length + 1 := length_filter_ne_ge l1 hnd1 i1
  have hlen0 : l0.length = 5 := List.length_finRange
  have hge : 3 ≤ l2.length := by omega
  match h : l2 with
  | j0 :: j1 :: j2 :: rest =>
    rw [List.nodup_cons] at hnd2
    rcases hnd2 with ⟨hj0_not, hnd2'⟩
    rw [List.nodup_cons] at hnd2'
    rcases hnd2' with ⟨hj1_not, _⟩
    have hmem : ∀ z, z ∈ l2 → z ≠ i0 ∧ z ≠ i1 := by
      intro z hz
      rw [List.mem_filter] at hz
      have h1 := bne_iff_ne.mp hz.2
      have hz1 := hz.1
      rw [List.mem_filter] at hz1
      exact ⟨bne_iff_ne.mp hz1.2, h1⟩
    have hm0 := hmem j0 (by rw [h]; exact List.mem_cons_self ..)
    have hm1 := hmem j1 (by rw [h]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hm2 := hmem j2 (by rw [h]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    exact ⟨j0, j1, j2,
      fun heq => hj0_not (heq ▸ List.mem_cons_self ..),
      fun heq => hj0_not (heq ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      fun heq => hj1_not (heq ▸ List.mem_cons_self ..),
      hm0.1, hm0.2, hm1.1, hm1.2, hm2.1, hm2.2⟩
  | [] => simp at hge
  | [_] => simp at hge
  | [_, _] => simp at hge

private theorem exists_three_outside4 (i0 i1 i2 i3 : Fin 7) :
    ∃ j0 j1 j2 : Fin 7,
      j0 ≠ j1 ∧ j0 ≠ j2 ∧ j1 ≠ j2 ∧
      j0 ≠ i0 ∧ j0 ≠ i1 ∧ j0 ≠ i2 ∧ j0 ≠ i3 ∧
      j1 ≠ i0 ∧ j1 ≠ i1 ∧ j1 ≠ i2 ∧ j1 ≠ i3 ∧
      j2 ≠ i0 ∧ j2 ≠ i1 ∧ j2 ≠ i2 ∧ j2 ≠ i3 := by
  let l0 := List.finRange 7
  let l1 := l0.filter (fun x => x != i0)
  let l2 := l1.filter (fun x => x != i1)
  let l3 := l2.filter (fun x => x != i2)
  let l4 := l3.filter (fun x => x != i3)
  have hnd0 : l0.Nodup := List.nodup_finRange 7
  have hnd1 : l1.Nodup := hnd0.filter _
  have hnd2 : l2.Nodup := hnd1.filter _
  have hnd3 : l3.Nodup := hnd2.filter _
  have hnd4 : l4.Nodup := hnd3.filter _
  have hlen1 : l0.length ≤ l1.length + 1 := length_filter_ne_ge l0 hnd0 i0
  have hlen2 : l1.length ≤ l2.length + 1 := length_filter_ne_ge l1 hnd1 i1
  have hlen3 : l2.length ≤ l3.length + 1 := length_filter_ne_ge l2 hnd2 i2
  have hlen4 : l3.length ≤ l4.length + 1 := length_filter_ne_ge l3 hnd3 i3
  have hlen0 : l0.length = 7 := List.length_finRange
  have hge : 3 ≤ l4.length := by omega
  match h : l4 with
  | j0 :: j1 :: j2 :: rest =>
    rw [List.nodup_cons] at hnd4
    rcases hnd4 with ⟨hj0_not, hnd4'⟩
    rw [List.nodup_cons] at hnd4'
    rcases hnd4' with ⟨hj1_not, _⟩
    have hmem : ∀ z, z ∈ l4 → z ≠ i0 ∧ z ≠ i1 ∧ z ≠ i2 ∧ z ≠ i3 := by
      intro z hz
      rw [List.mem_filter] at hz; have h3 := bne_iff_ne.mp hz.2
      have hz3 := hz.1; rw [List.mem_filter] at hz3; have h2 := bne_iff_ne.mp hz3.2
      have hz2 := hz3.1; rw [List.mem_filter] at hz2; have h1 := bne_iff_ne.mp hz2.2
      have hz1 := hz2.1; rw [List.mem_filter] at hz1; have h0 := bne_iff_ne.mp hz1.2
      exact ⟨h0, h1, h2, h3⟩
    have hm0 := hmem j0 (by rw [h]; exact List.mem_cons_self ..)
    have hm1 := hmem j1 (by rw [h]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hm2 := hmem j2 (by rw [h]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    exact ⟨j0, j1, j2,
      fun heq => hj0_not (heq ▸ List.mem_cons_self ..),
      fun heq => hj0_not (heq ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      fun heq => hj1_not (heq ▸ List.mem_cons_self ..),
      hm0.1, hm0.2.1, hm0.2.2.1, hm0.2.2.2,
      hm1.1, hm1.2.1, hm1.2.2.1, hm1.2.2.2,
      hm2.1, hm2.2.1, hm2.2.2.1, hm2.2.2.2⟩
  | [] => simp at hge
  | [_] => simp at hge
  | [_, _] => simp at hge

private theorem weight_mod_eight_of_depends2 (g : BitVec 5 → Bool) (hg : DependsOnAtMost2 g) :
    weight g % 8 = 0 := by
  rcases hg with ⟨i0, i1, hfn, hspec⟩
  rcases exists_three_outside2 i0 i1 with
    ⟨j0, j1, j2, h01, h02, h12, h0i0, h0i1, h1i0, h1i1, h2i0, h2i1⟩
  apply weight_mod_eight_of_three_flip_inv g j0 j1 j2 h01 h02 h12
  · intro x
    rw [hspec (flipBit x j0), hspec x,
        getLsbD_flipBit_ne x j0 i0 h0i0.symm, getLsbD_flipBit_ne x j0 i1 h0i1.symm]
  · intro x
    rw [hspec (flipBit x j1), hspec x,
        getLsbD_flipBit_ne x j1 i0 h1i0.symm, getLsbD_flipBit_ne x j1 i1 h1i1.symm]
  · intro x
    rw [hspec (flipBit x j2), hspec x,
        getLsbD_flipBit_ne x j2 i0 h2i0.symm, getLsbD_flipBit_ne x j2 i1 h2i1.symm]

private theorem weight_mod_eight_of_depends4 (g : BitVec 7 → Bool) (hg : DependsOnAtMost4 g) :
    weight g % 8 = 0 := by
  rcases hg with ⟨i0, i1, i2, i3, hfn, hspec⟩
  rcases exists_three_outside4 i0 i1 i2 i3 with
    ⟨j0, j1, j2, h01, h02, h12,
     h0i0, h0i1, h0i2, h0i3,
     h1i0, h1i1, h1i2, h1i3,
     h2i0, h2i1, h2i2, h2i3⟩
  apply weight_mod_eight_of_three_flip_inv g j0 j1 j2 h01 h02 h12
  · intro x
    rw [hspec (flipBit x j0), hspec x,
        getLsbD_flipBit_ne x j0 i0 h0i0.symm, getLsbD_flipBit_ne x j0 i1 h0i1.symm,
        getLsbD_flipBit_ne x j0 i2 h0i2.symm, getLsbD_flipBit_ne x j0 i3 h0i3.symm]
  · intro x
    rw [hspec (flipBit x j1), hspec x,
        getLsbD_flipBit_ne x j1 i0 h1i0.symm, getLsbD_flipBit_ne x j1 i1 h1i1.symm,
        getLsbD_flipBit_ne x j1 i2 h1i2.symm, getLsbD_flipBit_ne x j1 i3 h1i3.symm]
  · intro x
    rw [hspec (flipBit x j2), hspec x,
        getLsbD_flipBit_ne x j2 i0 h2i0.symm, getLsbD_flipBit_ne x j2 i1 h2i1.symm,
        getLsbD_flipBit_ne x j2 i2 h2i2.symm, getLsbD_flipBit_ne x j2 i3 h2i3.symm]

/-! ## Section 2: Theorem 1 — 0-`LOP3` 2-Trit / 4-Bit → E2M1 Unpacker -/

theorem unpack_2t4b_to_e2m1_zero_lop3 (w0 w1 : Int)
    (hw0 : IsTrit w0) (hw1 : IsTrit w1) :
    let (n0, n1) := unpack2t4b (encode2t4b w0 w1)
    e2m1TwiceVal n0 = 2 * w0 ∧ e2m1TwiceVal n1 = 2 * w1 := by
  rcases hw0 with rfl | rfl | rfl <;> rcases hw1 with rfl | rfl | rfl <;> decide

/-! ## Section 3: Theorem 2 — Exact 4-`LOP3` 3-Trit / 5-Bit → E2M1 Unpacker -/

theorem unpack_3t5b_to_e2m1_four_lop3 (w0 w1 w2 : Int)
    (hw0 : IsTrit w0) (hw1 : IsTrit w1) (hw2 : IsTrit w2) :
    let (n0, n1, n2) := unpack3t5b (encode3t5b w0 w1 w2)
    e2m1TwiceVal n0 = 2 * w0 ∧ e2m1TwiceVal n1 = 2 * w1 ∧ e2m1TwiceVal n2 = 2 * w2 := by
  rcases hw0 with rfl | rfl | rfl <;>
  rcases hw1 with rfl | rfl | rfl <;>
  rcases hw2 with rfl | rfl | rfl <;>
  decide

/-! ## Section 4: Theorem 3 — Exact ≥3-`LOP3` Lower Bound for 3-Trit / 5-Bit → E2M1 -/

private def fin3ToTrit (t : Fin 3) : Int := (t.val : Int) - 1

private theorem fin3ToTrit_isTrit (t : Fin 3) : IsTrit (fin3ToTrit t) := by
  rcases t with ⟨v, hv⟩
  unfold fin3ToTrit IsTrit
  match v, hv with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr (Or.inl rfl)
  | 2, _ => exact Or.inr (Or.inr rfl)

private theorem fin3ToTrit_inj {a b : Fin 3} (h : fin3ToTrit a = fin3ToTrit b) : a = b := by
  unfold fin3ToTrit at h
  exact Fin.ext (by omega)

private def nzTrit (b : Fin 2) : Int := if b.val == 0 then -1 else 1

private theorem nzTrit_isTrit (b : Fin 2) : IsTrit (nzTrit b) := by
  rcases b with ⟨v, hv⟩
  match v, hv with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr (Or.inr rfl)

private theorem nzTrit_ne_zero (b : Fin 2) : 2 * nzTrit b ≠ 0 := by
  rcases b with ⟨v, hv⟩
  match v, hv with
  | 0, _ => simp [nzTrit]
  | 1, _ => simp [nzTrit]

private theorem nzTrit_inj {a b : Fin 2} (h : 2 * nzTrit a = 2 * nzTrit b) : a = b := by
  rcases a with ⟨va, hva⟩
  rcases b with ⟨vb, hvb⟩
  match va, hva, vb, hvb with
  | 0, _, 0, _ => rfl
  | 1, _, 1, _ => rfl
  | 0, _, 1, _ => simp [nzTrit] at h
  | 1, _, 0, _ => simp [nzTrit] at h

private theorem trit_slot_weight_bounds
    (dec : BitVec 5 → BitVec 4 × BitVec 4 × BitVec 4)
    (hsurj : ∀ w0 w1 w2 : Int, IsTrit w0 → IsTrit w1 → IsTrit w2 →
      ∃ x : BitVec 5, decode3E2M1 (dec x) = (2 * w0, 2 * w1, 2 * w2))
    (s : Fin 3) :
    let f : BitVec 5 → Bool := fun x =>
      match s with
      | ⟨0, _⟩ => e2m1TwiceVal (dec x).1 != 0
      | ⟨1, _⟩ => e2m1TwiceVal (dec x).2.1 != 0
      | ⟨2, _⟩ => e2m1TwiceVal (dec x).2.2 != 0
    18 ≤ weight f ∧ weight f ≤ 23 := by
  intro f
  let place (s' : Fin 3) (v u1 u2 : Int) : Int × Int × Int :=
    match s' with
    | ⟨0, _⟩ => (v, u1, u2)
    | ⟨1, _⟩ => (u1, v, u2)
    | ⟨2, _⟩ => (u1, u2, v)
  have hplace_inj : ∀ (s' : Fin 3) v u1 u2 v' u1' u2',
      place s' v u1 u2 = place s' v' u1' u2' → v = v' ∧ u1 = u1' ∧ u2 = u2' := by
    intro s' v u1 u2 v' u1' u2' h
    rcases s' with ⟨sv, hsv⟩
    match sv, hsv with
    | 0, _ =>
      simp only [place, Prod.mk.injEq] at h
      exact ⟨h.1, h.2.1, h.2.2⟩
    | 1, _ =>
      simp only [place, Prod.mk.injEq] at h
      exact ⟨h.2.1, h.1, h.2.2⟩
    | 2, _ =>
      simp only [place, Prod.mk.injEq] at h
      exact ⟨h.2.2, h.1, h.2.1⟩
  have hplace_surj : ∀ (s' : Fin 3) v u1 u2, IsTrit v → IsTrit u1 → IsTrit u2 →
      ∃ x : BitVec 5, decode3E2M1 (dec x) = place s' (2 * v) (2 * u1) (2 * u2) := by
    intro s' v u1 u2 hv hu1 hu2
    rcases s' with ⟨sv, hsv⟩
    match sv, hsv with
    | 0, _ => exact hsurj v u1 u2 hv hu1 hu2
    | 1, _ => exact hsurj u1 v u2 hu1 hv hu2
    | 2, _ => exact hsurj u1 u2 v hu1 hu2 hv
  have hproj_eq : ∀ x v u1 u2, decode3E2M1 (dec x) = place s v u1 u2 → f x = (v != 0) := by
    intro x v u1 u2 h
    dsimp only [f]
    rcases s with ⟨sv, hsv⟩
    match sv, hsv with
    | 0, _ =>
      simp only [decode3E2M1, place, Prod.mk.injEq] at h
      simp [h.1]
    | 1, _ =>
      simp only [decode3E2M1, place, Prod.mk.injEq] at h
      simp [h.2.1]
    | 2, _ =>
      simp only [decode3E2M1, place, Prod.mk.injEq] at h
      simp [h.2.2]
  have h18 : 18 ≤ weight f := by
    let target : Fin 18 → Int × Int × Int := fun a =>
      let b  : Fin 2 := ⟨a.val / 9, by omega⟩
      let u1 : Fin 3 := ⟨(a.val % 9) / 3, by omega⟩
      let u2 : Fin 3 := ⟨a.val % 3, by omega⟩
      place s (2 * nzTrit b) (2 * fin3ToTrit u1) (2 * fin3ToTrit u2)
    apply le_weight_of_exists f (fun x => decode3E2M1 (dec x)) target
    · intro a b hab
      have hp := hplace_inj s _ _ _ _ _ _ hab
      have hb := congrArg Fin.val (nzTrit_inj hp.1)
      have h1 := congrArg Fin.val (fin3ToTrit_inj (by omega : fin3ToTrit ⟨(a.val % 9) / 3, by omega⟩ = fin3ToTrit ⟨(b.val % 9) / 3, by omega⟩))
      have h2 := congrArg Fin.val (fin3ToTrit_inj (by omega : fin3ToTrit ⟨a.val % 3, by omega⟩ = fin3ToTrit ⟨b.val % 3, by omega⟩))
      dsimp only at hb h1 h2
      exact Fin.ext (by omega)
    · intro a
      exact hplace_surj s (nzTrit ⟨a.val / 9, by omega⟩)
        (fin3ToTrit ⟨(a.val % 9) / 3, by omega⟩)
        (fin3ToTrit ⟨a.val % 3, by omega⟩)
        (nzTrit_isTrit _) (fin3ToTrit_isTrit _) (fin3ToTrit_isTrit _)
    · intro x a hx
      rw [hproj_eq x _ _ _ hx]
      exact bne_iff_ne.mpr (nzTrit_ne_zero ⟨a.val / 9, by omega⟩)
  have h9 : 9 ≤ weight (fun x => !f x) := by
    let target : Fin 9 → Int × Int × Int := fun a =>
      let u1 : Fin 3 := ⟨a.val / 3, by omega⟩
      let u2 : Fin 3 := ⟨a.val % 3, by omega⟩
      place s (2 * 0) (2 * fin3ToTrit u1) (2 * fin3ToTrit u2)
    apply le_weight_of_exists (fun x => !f x) (fun x => decode3E2M1 (dec x)) target
    · intro a b hab
      have hp := hplace_inj s _ _ _ _ _ _ hab
      have h1 := congrArg Fin.val (fin3ToTrit_inj (by omega : fin3ToTrit ⟨a.val / 3, by omega⟩ = fin3ToTrit ⟨b.val / 3, by omega⟩))
      have h2 := congrArg Fin.val (fin3ToTrit_inj (by omega : fin3ToTrit ⟨a.val % 3, by omega⟩ = fin3ToTrit ⟨b.val % 3, by omega⟩))
      dsimp only at h1 h2
      exact Fin.ext (by omega)
    · intro a
      exact hplace_surj s 0
        (fin3ToTrit ⟨a.val / 3, by omega⟩)
        (fin3ToTrit ⟨a.val % 3, by omega⟩)
        (Or.inr (Or.inl rfl)) (fin3ToTrit_isTrit _) (fin3ToTrit_isTrit _)
    · intro x a hx
      rw [hproj_eq x _ _ _ hx]
      rfl
  have hsum : weight f + weight (fun x => !f x) = 32 := weight_add_not f
  omega

theorem unpack_3t5b_to_e2m1_three_gate_lower_bound
    (dec : BitVec 5 → BitVec 4 × BitVec 4 × BitVec 4)
    (hsurj : ∀ w0 w1 w2 : Int, IsTrit w0 → IsTrit w1 → IsTrit w2 →
      ∃ x : BitVec 5, decode3E2M1 (dec x) = (2 * w0, 2 * w1, 2 * w2)) :
    let f0 : BitVec 5 → Bool := fun x => e2m1TwiceVal (dec x).1 != 0
    let f1 : BitVec 5 → Bool := fun x => e2m1TwiceVal (dec x).2.1 != 0
    let f2 : BitVec 5 → Bool := fun x => e2m1TwiceVal (dec x).2.2 != 0
    (18 ≤ weight f0 ∧ weight f0 ≤ 23) ∧
    (18 ≤ weight f1 ∧ weight f1 ≤ 23) ∧
    (18 ≤ weight f2 ∧ weight f2 ≤ 23) ∧
    (∀ g : BitVec 5 → Bool, DependsOnAtMost2 g → weight g % 8 = 0) ∧
    (¬ DependsOnAtMost2 f0 ∧ ¬ DependsOnAtMost2 f1 ∧ ¬ DependsOnAtMost2 f2) ∧
    (f0 ≠ f1 ∧ f0 ≠ f2 ∧ f1 ≠ f2) := by
  intro f0 f1 f2
  have hb0 : 18 ≤ weight f0 ∧ weight f0 ≤ 23 := trit_slot_weight_bounds dec hsurj ⟨0, by omega⟩
  have hb1 : 18 ≤ weight f1 ∧ weight f1 ≤ 23 := trit_slot_weight_bounds dec hsurj ⟨1, by omega⟩
  have hb2 : 18 ≤ weight f2 ∧ weight f2 ≤ 23 := trit_slot_weight_bounds dec hsurj ⟨2, by omega⟩
  have hmod : ∀ g : BitVec 5 → Bool, DependsOnAtMost2 g → weight g % 8 = 0 :=
    weight_mod_eight_of_depends2
  have hnd0 : ¬ DependsOnAtMost2 f0 := fun h => by have := hmod f0 h; omega
  have hnd1 : ¬ DependsOnAtMost2 f1 := fun h => by have := hmod f1 h; omega
  have hnd2 : ¬ DependsOnAtMost2 f2 := fun h => by have := hmod f2 h; omega
  have hne01 : f0 ≠ f1 := by
    intro heq
    rcases hsurj 1 0 0 (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl)) with ⟨x, hx⟩
    simp only [decode3E2M1, Prod.mk.injEq] at hx
    have hfx := congrFun heq x
    simp [f0, f1, hx.1, hx.2.1] at hfx
  have hne02 : f0 ≠ f2 := by
    intro heq
    rcases hsurj 1 0 0 (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl)) with ⟨x, hx⟩
    simp only [decode3E2M1, Prod.mk.injEq] at hx
    have hfx := congrFun heq x
    simp [f0, f2, hx.1, hx.2.2] at hfx
  have hne12 : f1 ≠ f2 := by
    intro heq
    rcases hsurj 0 1 0 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) with ⟨x, hx⟩
    simp only [decode3E2M1, Prod.mk.injEq] at hx
    have hfx := congrFun heq x
    simp [f1, f2, hx.2.1, hx.2.2] at hfx
  exact ⟨hb0, hb1, hb2, hmod, ⟨hnd0, hnd1, hnd2⟩, ⟨hne01, hne02, hne12⟩⟩

/-! ## Section 5: Theorem 4 — 3-Quinary / 7-Bit 5-Variable Support Barrier -/

private theorem nodup_getElem_inj {α : Type} :
    ∀ {l : List α}, l.Nodup → ∀ {i j : Nat} (hi : i < l.length) (hj : j < l.length),
      l[i]'hi = l[j]'hj → i = j
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | a :: t, hnd, 0, 0, _, _, _ => rfl
  | a :: t, hnd, 0, j + 1, _, hj, heq => by
    rw [List.nodup_cons] at hnd
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
    have hm : t[j]'(Nat.lt_of_succ_lt_succ hj) ∈ t := List.getElem_mem _
    exact absurd (heq ▸ hm) hnd.1
  | a :: t, hnd, i + 1, 0, hi, _, heq => by
    rw [List.nodup_cons] at hnd
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
    have hm : t[i]'(Nat.lt_of_succ_lt_succ hi) ∈ t := List.getElem_mem _
    exact absurd (heq.symm ▸ hm) hnd.1
  | a :: t, hnd, i + 1, j + 1, hi, hj, heq => by
    rw [List.nodup_cons] at hnd
    exact congrArg Nat.succ (nodup_getElem_inj hnd.2 _ _ heq)

private theorem quinary_slot_lb
    (dec : BitVec 7 → Fin 5 × Fin 5 × Fin 5)
    (hsurj : ∀ q0 q1 q2 : Fin 5, ∃ x : BitVec 7, dec x = (q0, q1, q2))
    (s : Fin 3) (Q : Fin 5 → Bool) :
    25 * countFin5 Q ≤ weight (fun x => Q (slot3 s (dec x))) := by
  let vals := (List.finRange 5).filter Q
  have hlen : vals.length = countFin5 Q := by
    unfold countFin5
    rw [List.countP_eq_length_filter]
  have hnd : vals.Nodup := (List.nodup_finRange 5).filter Q
  let place (s' : Fin 3) (v u1 u2 : Fin 5) : Fin 5 × Fin 5 × Fin 5 :=
    match s' with
    | ⟨0, _⟩ => (v, u1, u2)
    | ⟨1, _⟩ => (u1, v, u2)
    | ⟨2, _⟩ => (u1, u2, v)
  have hplace_inj : ∀ (s' : Fin 3) v u1 u2 v' u1' u2',
      place s' v u1 u2 = place s' v' u1' u2' → v = v' ∧ u1 = u1' ∧ u2 = u2' := by
    intro s' v u1 u2 v' u1' u2' h
    rcases s' with ⟨sv, hsv⟩
    match sv, hsv with
    | 0, _ => simp only [place, Prod.mk.injEq] at h; exact ⟨h.1, h.2.1, h.2.2⟩
    | 1, _ => simp only [place, Prod.mk.injEq] at h; exact ⟨h.2.1, h.1, h.2.2⟩
    | 2, _ => simp only [place, Prod.mk.injEq] at h; exact ⟨h.2.2, h.1, h.2.1⟩
  have hslot_place : ∀ (s' : Fin 3) v u1 u2, slot3 s' (place s' v u1 u2) = v := by
    intro s' v u1 u2
    rcases s' with ⟨sv, hsv⟩
    match sv, hsv with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
  let target : Fin (25 * countFin5 Q) → Fin 5 × Fin 5 × Fin 5 := fun a =>
    let idx : Nat := a.val / 25
    let hidx : idx < vals.length := by rw [hlen]; omega
    let v  : Fin 5 := vals[idx]'hidx
    let u1 : Fin 5 := ⟨(a.val % 25) / 5, by omega⟩
    let u2 : Fin 5 := ⟨a.val % 5, by omega⟩
    place s v u1 u2
  apply le_weight_of_exists (fun x => Q (slot3 s (dec x))) dec target
  · intro a b hab
    have hp := hplace_inj s _ _ _ _ _ _ hab
    have hidx_eq : a.val / 25 = b.val / 25 :=
      nodup_getElem_inj hnd (by rw [hlen]; omega) (by rw [hlen]; omega) hp.1
    have hu1 : (a.val % 25) / 5 = (b.val % 25) / 5 := congrArg Fin.val hp.2.1
    have hu2 : a.val % 5 = b.val % 5 := congrArg Fin.val hp.2.2
    exact Fin.ext (by omega)
  · intro a
    let t := target a
    exact hsurj t.1 t.2.1 t.2.2
  · intro x a hx
    rw [hx]
    dsimp only [target]
    rw [hslot_place]
    have hmem : vals[a.val / 25]'(by rw [hlen]; omega) ∈ vals := List.getElem_mem _
    exact (List.mem_filter.mp hmem).2

theorem quinary_3w7b_five_var_impossibility
    (dec : BitVec 7 → Fin 5 × Fin 5 × Fin 5)
    (hsurj : ∀ q0 q1 q2 : Fin 5, ∃ x : BitVec 7, dec x = (q0, q1, q2)) :
    (∀ (s : Fin 3) (P : Fin 5 → Bool),
      1 ≤ countFin5 P → countFin5 P ≤ 4 →
      let k := countFin5 P
      let f : BitVec 7 → Bool := fun x => P (slot3 s (dec x))
      25 * k ≤ weight f ∧ weight f ≤ 25 * k + 3 ∧ weight f % 8 ≠ 0) ∧
    (∀ g : BitVec 7 → Bool, DependsOnAtMost4 g → weight g % 8 = 0) ∧
    (∀ (s : Fin 3) (P : Fin 5 → Bool),
      1 ≤ countFin5 P → countFin5 P ≤ 4 →
      ¬ DependsOnAtMost4 (fun x => P (slot3 s (dec x)))) := by
  have hbounds : ∀ (s : Fin 3) (P : Fin 5 → Bool),
      1 ≤ countFin5 P → countFin5 P ≤ 4 →
      let k := countFin5 P
      let f : BitVec 7 → Bool := fun x => P (slot3 s (dec x))
      25 * k ≤ weight f ∧ weight f ≤ 25 * k + 3 ∧ weight f % 8 ≠ 0 := by
    intro s P hk1 hk4
    intro k f
    have hlb : 25 * k ≤ weight f := quinary_slot_lb dec hsurj s P
    have hnot : 25 * countFin5 (fun q => !P q) ≤ weight (fun x => !f x) :=
      quinary_slot_lb dec hsurj s (fun q => !P q)
    have hkc : k + countFin5 (fun q => !P q) = 5 := by
      unfold k countFin5
      rw [countP_add_not, List.length_finRange]
    have hsum : weight f + weight (fun x => !f x) = 128 := weight_add_not f
    have hub : weight f ≤ 25 * k + 3 := by omega
    have hmod8 : weight f % 8 ≠ 0 := by
      have hk1' : 1 ≤ k := hk1
      have hk4' : k ≤ 4 := hk4
      have hcases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases hcases with hk | hk | hk | hk <;> omega
    exact ⟨hlb, hub, hmod8⟩
  have hmod : ∀ g : BitVec 7 → Bool, DependsOnAtMost4 g → weight g % 8 = 0 :=
    weight_mod_eight_of_depends4
  refine ⟨hbounds, hmod, ?_⟩
  intro s P hk1 hk4 hdep
  have h1 := (hbounds s P hk1 hk4).2.2
  have h2 := hmod _ hdep
  exact h1 h2

/-! ## Section 6: Theorem 5 — Bijective 2-Bit Asymmetric Codebook & Polarity Flip -/

private theorem asym2_foldl_aux (xs : List (Bool × Bool × Int)) (acc0 acc1 acc2 : Int) :
    xs.foldl (fun acc (b1, b0, a) => acc + asym2Val b1 b0 * a) (acc0 + acc1 - 2 * acc2) =
    acc0 +
      xs.foldl (fun acc (_, b0, a) => acc + (if b0 then a else 0)) acc1 -
      2 * xs.foldl (fun acc (b1, _, a) => acc + (if b1 then a else 0)) acc2 := by
  induction xs generalizing acc0 acc1 acc2 with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨b1, b0, a⟩
    simp only [List.foldl_cons]
    have hstep :
        (acc0 + acc1 - 2 * acc2) + asym2Val b1 b0 * a =
        acc0 + (acc1 + (if b0 then a else 0)) - 2 * (acc2 + (if b1 then a else 0)) := by
      cases b1 <;> cases b0 <;> simp [asym2Val] <;> omega
    rw [hstep]
    exact ih acc0 (acc1 + (if b0 then a else 0)) (acc2 + (if b1 then a else 0))

theorem asymmetric_2bit_polarity_flip_exact :
    (asym2Val false false = 0) ∧
    (∀ b1 b0 b1' b0' : Bool, asym2Val b1 b0 = asym2Val b1' b0' → b1 = b1' ∧ b0 = b0') ∧
    (∀ v : Int, (v = -2 ∨ v = -1 ∨ v = 0 ∨ v = 1) ↔ ∃ b1 b0 : Bool, asym2Val b1 b0 = v) ∧
    (∀ v : Int, (v = -1 ∨ v = 0 ∨ v = 1 ∨ v = 2) ↔ ∃ b1 b0 : Bool, -asym2Val b1 b0 = v) ∧
    (∀ xs : List (Bool × Bool × Int),
      xs.foldl (fun acc (b1, b0, a) => acc + asym2Val b1 b0 * a) 0 =
      xs.foldl (fun acc (_, b0, a) => acc + (if b0 then a else 0)) 0 -
      2 * xs.foldl (fun acc (b1, _, a) => acc + (if b1 then a else 0)) 0) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro b1 b0 b1' b0' h
    cases b1 <;> cases b0 <;> cases b1' <;> cases b0' <;> simp [asym2Val] at h ⊢
  · intro v
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨true, false, rfl⟩
      · exact ⟨true, true, rfl⟩
      · exact ⟨false, false, rfl⟩
      · exact ⟨false, true, rfl⟩
    · rintro ⟨b1, b0, rfl⟩
      cases b1 <;> cases b0 <;> decide
  · intro v
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨false, true, rfl⟩
      · exact ⟨false, false, rfl⟩
      · exact ⟨true, true, rfl⟩
      · exact ⟨true, false, rfl⟩
    · rintro ⟨b1, b0, rfl⟩
      cases b1 <;> cases b0 <;> decide
  · intro xs
    have h := asym2_foldl_aux xs 0 0 0
    simpa using h

/-! ## Section 7: Theorem 6 — 4:2 vs 3:2 Compressor `LOP3` Depth Inversion -/

private theorem exists_missing_fin5 (i j k : Fin 5) :
    ∃ m : Fin 5, m ≠ i ∧ m ≠ j ∧ m ≠ k := by
  let l0 := List.finRange 5
  let l1 := l0.filter (fun x => x != i)
  let l2 := l1.filter (fun x => x != j)
  let l3 := l2.filter (fun x => x != k)
  have hnd0 : l0.Nodup := List.nodup_finRange 5
  have hnd1 : l1.Nodup := hnd0.filter _
  have hnd2 : l2.Nodup := hnd1.filter _
  have hlen1 : l0.length ≤ l1.length + 1 := length_filter_ne_ge l0 hnd0 i
  have hlen2 : l1.length ≤ l2.length + 1 := length_filter_ne_ge l1 hnd1 j
  have hlen3 : l2.length ≤ l3.length + 1 := length_filter_ne_ge l2 hnd2 k
  have hlen0 : l0.length = 5 := List.length_finRange
  have hge : 1 ≤ l3.length := by omega
  match h : l3 with
  | m :: _ =>
    have hm : m ∈ l3 := by rw [h]; exact List.mem_cons_self ..
    rw [List.mem_filter] at hm; have hk := bne_iff_ne.mp hm.2
    have hm2 := hm.1; rw [List.mem_filter] at hm2; have hj := bne_iff_ne.mp hm2.2
    have hm1 := hm2.1; rw [List.mem_filter] at hm1; have hi := bne_iff_ne.mp hm1.2
    exact ⟨m, hi, hj, hk⟩
  | [] => simp at hge

private theorem sum4to2_indicator (m : Fin 5) :
    sum4to2 (⟨0, by omega⟩ == m) (⟨1, by omega⟩ == m) (⟨2, by omega⟩ == m)
      (⟨3, by omega⟩ == m) (⟨4, by omega⟩ == m) = true := by
  rcases m with ⟨mv, hmv⟩
  match mv, hmv with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem compressor_4to2_lop3_depth_inversion :
    (∀ i j k : Fin 5, ∀ imm : UInt8,
      ∃ v : Fin 5 → Bool,
        lop3 imm (v i) (v j) (v k) ≠ sum4to2 (v 0) (v 1) (v 2) (v 3) (v 4)) ∧
    (∀ a b c : Bool,
      (if sum3to2 a b c then (1 : Nat) else 0) + 2 * (if carry3to2 a b c then 1 else 0) =
      (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)) := by
  constructor
  · intro i j k imm
    rcases exists_missing_fin5 i j k with ⟨m, hmi, hmj, hmk⟩
    let v0 : Fin 5 → Bool := fun _ => false
    let v1 : Fin 5 → Bool := fun r => r == m
    have hi : v1 i = false := beq_eq_false_iff_ne.mpr hmi.symm
    have hj : v1 j = false := beq_eq_false_iff_ne.mpr hmj.symm
    have hk : v1 k = false := beq_eq_false_iff_ne.mpr hmk.symm
    cases hval : lop3 imm false false false
    · refine ⟨v1, ?_⟩
      simp only [hi, hj, hk, hval]
      have hs : sum4to2 (v1 0) (v1 1) (v1 2) (v1 3) (v1 4) = true := sum4to2_indicator m
      rw [hs]
      decide
    · refine ⟨v0, ?_⟩
      simp only [v0, hval]
      decide
  · decide

end SubbyteE2M1Lop3
