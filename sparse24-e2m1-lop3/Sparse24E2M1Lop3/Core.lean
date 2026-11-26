/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sparse24E2M1Lop3.Defs

/-!
# Core Combinatorial, Pigeonhole & Bit-Flip Involution Lemmas

Pure-`Init` (zero Mathlib, zero `native_decide`) lemmas shared across the lower-bound proofs:
- `weight_add_not`, `weight_split`
- `le_weight_of_inj`, `le_weight_of_exists`
- `weight_mod_sixteen_of_four_flip_inv` (`16 ∣ weight f` for 4-flip-invariant Boolean functions)
- `exists_four_outside4` (4 distinct coordinates in `Fin 8` outside any 4-element subset)
- Exact wire-fiber weights on `BitVec 3` and `BitVec 5`.
-/

namespace Sparse24E2M1Lop3

theorem countP_add_not {α : Type} (l : List α) (f : α → Bool) :
    l.countP f + l.countP (fun x => !f x) = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.countP_cons, List.length_cons]
    cases f a <;> simp <;> omega

theorem weight_add_not {k : Nat} (f : BitVec k → Bool) :
    weight f + weight (fun x => !f x) = 2 ^ k := by
  unfold weight
  rw [countP_add_not, List.length_finRange]

theorem countP_split {α : Type} (l : List α) (P Q : α → Bool) :
    l.countP P = l.countP (fun x => P x && Q x) + l.countP (fun x => P x && !Q x) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.countP_cons]
    cases P a <;> cases Q a <;> simp <;> omega

theorem weight_split {k : Nat} (P Q : BitVec k → Bool) :
    weight P = weight (fun x => P x && Q x) + weight (fun x => P x && !Q x) :=
  countP_split (List.finRange (2 ^ k)) (fun i => P (BitVec.ofNat k i.val))
    (fun i => Q (BitVec.ofNat k i.val))

theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] :
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

theorem le_weight_of_inj {m k : Nat} (f : BitVec k → Bool)
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

theorem le_weight_of_exists {α : Type} {m k : Nat} (f : BitVec k → Bool)
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

def flipBit {k : Nat} (x : BitVec k) (j : Fin k) : BitVec k :=
  x ^^^ BitVec.ofNat k (1 <<< j.val)

theorem flipBit_involutive {k : Nat} (x : BitVec k) (j : Fin k) :
    flipBit (flipBit x j) j = x := by
  unfold flipBit
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem getLsbD_one_shiftLeft {k : Nat} (j : Fin k) (i : Nat) :
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

theorem getLsbD_flipBit_self {k : Nat} (x : BitVec k) (j : Fin k) :
    (flipBit x j).getLsbD j.val = !x.getLsbD j.val := by
  unfold flipBit
  rw [BitVec.getLsbD_xor, getLsbD_one_shiftLeft]
  simp

theorem getLsbD_flipBit_ne {k : Nat} (x : BitVec k) (j i : Fin k) (h : i ≠ j) :
    (flipBit x j).getLsbD i.val = x.getLsbD i.val := by
  unfold flipBit
  rw [BitVec.getLsbD_xor, getLsbD_one_shiftLeft]
  have hne : i.val ≠ j.val := fun he => h (Fin.ext he)
  simp [hne]

theorem weight_le_of_flip_inv_dir {k : Nat} (f : BitVec k → Bool) (j : Fin k) (b : Bool)
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

theorem weight_double_of_flip_inv {k : Nat} (f : BitVec k → Bool) (j : Fin k)
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

theorem weight_mod_sixteen_of_four_flip_inv {k : Nat} (f : BitVec k → Bool)
    (j0 j1 j2 j3 : Fin k)
    (h01 : j0 ≠ j1) (h02 : j0 ≠ j2) (h03 : j0 ≠ j3)
    (h12 : j1 ≠ j2) (h13 : j1 ≠ j3) (h23 : j2 ≠ j3)
    (hinv0 : ∀ x, f (flipBit x j0) = f x)
    (hinv1 : ∀ x, f (flipBit x j1) = f x)
    (hinv2 : ∀ x, f (flipBit x j2) = f x)
    (hinv3 : ∀ x, f (flipBit x j3) = f x) :
    weight f % 16 = 0 := by
  let f1 : BitVec k → Bool := fun x => f x && !x.getLsbD j0.val
  let f2 : BitVec k → Bool := fun x => f1 x && !x.getLsbD j1.val
  let f3 : BitVec k → Bool := fun x => f2 x && !x.getLsbD j2.val
  have hw0 : weight f = 2 * weight f1 := weight_double_of_flip_inv f j0 hinv0
  have hinv1' : ∀ x, f1 (flipBit x j1) = f1 x := by
    intro x
    simp only [f1, hinv1 x, getLsbD_flipBit_ne x j1 j0 h01]
  have hw1 : weight f1 = 2 * weight f2 := weight_double_of_flip_inv f1 j1 hinv1'
  have hinv2' : ∀ x, f2 (flipBit x j2) = f2 x := by
    intro x
    simp only [f2, f1, hinv2 x, getLsbD_flipBit_ne x j2 j0 h02, getLsbD_flipBit_ne x j2 j1 h12]
  have hw2 : weight f2 = 2 * weight f3 := weight_double_of_flip_inv f2 j2 hinv2'
  have hinv3' : ∀ x, f3 (flipBit x j3) = f3 x := by
    intro x
    simp only [f3, f2, f1, hinv3 x, getLsbD_flipBit_ne x j3 j0 h03,
      getLsbD_flipBit_ne x j3 j1 h13, getLsbD_flipBit_ne x j3 j2 h23]
  have hw3 : weight f3 = 2 * weight (fun x => f3 x && !x.getLsbD j3.val) :=
    weight_double_of_flip_inv f3 j3 hinv3'
  omega

theorem length_filter_ne_ge {α : Type} [DecidableEq α] (l : List α) (hnd : l.Nodup)
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

theorem exists_four_outside4 (i0 i1 i2 i3 : Fin 8) :
    ∃ j0 j1 j2 j3 : Fin 8,
      j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 ∧
      j0 ≠ i0 ∧ j0 ≠ i1 ∧ j0 ≠ i2 ∧ j0 ≠ i3 ∧
      j1 ≠ i0 ∧ j1 ≠ i1 ∧ j1 ≠ i2 ∧ j1 ≠ i3 ∧
      j2 ≠ i0 ∧ j2 ≠ i1 ∧ j2 ≠ i2 ∧ j2 ≠ i3 ∧
      j3 ≠ i0 ∧ j3 ≠ i1 ∧ j3 ≠ i2 ∧ j3 ≠ i3 := by
  let l0 := List.finRange 8
  let l1 := l0.filter (fun x => x != i0)
  let l2 := l1.filter (fun x => x != i1)
  let l3 := l2.filter (fun x => x != i2)
  let l4 := l3.filter (fun x => x != i3)
  have hnd0 : l0.Nodup := List.nodup_finRange 8
  have hnd1 : l1.Nodup := hnd0.filter _
  have hnd2 : l2.Nodup := hnd1.filter _
  have hnd3 : l3.Nodup := hnd2.filter _
  have hnd4 : l4.Nodup := hnd3.filter _
  have hlen1 : l0.length ≤ l1.length + 1 := length_filter_ne_ge l0 hnd0 i0
  have hlen2 : l1.length ≤ l2.length + 1 := length_filter_ne_ge l1 hnd1 i1
  have hlen3 : l2.length ≤ l3.length + 1 := length_filter_ne_ge l2 hnd2 i2
  have hlen4 : l3.length ≤ l4.length + 1 := length_filter_ne_ge l3 hnd3 i3
  have hlen0 : l0.length = 8 := List.length_finRange
  have hge : 4 ≤ l4.length := by omega
  match h : l4 with
  | j0 :: j1 :: j2 :: j3 :: rest =>
    rw [List.nodup_cons] at hnd4
    rcases hnd4 with ⟨hj0_not, hnd4'⟩
    rw [List.nodup_cons] at hnd4'
    rcases hnd4' with ⟨hj1_not, hnd4''⟩
    rw [List.nodup_cons] at hnd4''
    rcases hnd4'' with ⟨hj2_not, _⟩
    have hmem : ∀ z, z ∈ l4 → z ≠ i0 ∧ z ≠ i1 ∧ z ≠ i2 ∧ z ≠ i3 := by
      intro z hz
      rw [List.mem_filter] at hz
      have h3 := bne_iff_ne.mp hz.2
      have hz3 := hz.1
      rw [List.mem_filter] at hz3
      have h2 := bne_iff_ne.mp hz3.2
      have hz2 := hz3.1
      rw [List.mem_filter] at hz2
      have h1 := bne_iff_ne.mp hz2.2
      have hz1 := hz2.1
      rw [List.mem_filter] at hz1
      exact ⟨bne_iff_ne.mp hz1.2, h1, h2, h3⟩
    have hm0 := hmem j0 (by rw [h]; exact List.mem_cons_self ..)
    have hm1 := hmem j1 (by rw [h]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hm2 := hmem j2 (by rw [h]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have hm3 := hmem j3 (by rw [h]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    refine ⟨j0, j1, j2, j3,
      fun heq => hj0_not (heq ▸ List.mem_cons_self ..),
      fun heq => hj0_not (heq ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      fun heq => hj0_not (heq ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
      fun heq => hj1_not (heq ▸ List.mem_cons_self ..),
      fun heq => hj1_not (heq ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      fun heq => hj2_not (heq ▸ List.mem_cons_self ..),
      hm0.1, hm0.2.1, hm0.2.2.1, hm0.2.2.2,
      hm1.1, hm1.2.1, hm1.2.2.1, hm1.2.2.2,
      hm2.1, hm2.2.1, hm2.2.2.1, hm2.2.2.2,
      hm3.1, hm3.2.1, hm3.2.2.1, hm3.2.2.2⟩
  | [] => simp at hge
  | [_] => simp at hge
  | [_, _] => simp at hge
  | [_, _, _] => simp at hge

/-- Every Boolean function on `BitVec 8` depending on at most 4 input bits has `weight g % 16 = 0`. -/
theorem weight_mod_sixteen_of_dependsOnAtMost4 (g : BitVec 8 → Bool) (hg : DependsOnAtMost4 g) :
    weight g % 16 = 0 := by
  rcases hg with ⟨i0, i1, i2, i3, hfn, hdef⟩
  rcases exists_four_outside4 i0 i1 i2 i3 with
    ⟨j0, j1, j2, j3, h01, h02, h03, h12, h13, h23,
     h0i0, h0i1, h0i2, h0i3, h1i0, h1i1, h1i2, h1i3,
     h2i0, h2i1, h2i2, h2i3, h3i0, h3i1, h3i2, h3i3⟩
  apply weight_mod_sixteen_of_four_flip_inv g j0 j1 j2 j3 h01 h02 h03 h12 h13 h23
  · intro x
    rw [hdef (flipBit x j0), hdef x,
        getLsbD_flipBit_ne x j0 i0 h0i0.symm, getLsbD_flipBit_ne x j0 i1 h0i1.symm,
        getLsbD_flipBit_ne x j0 i2 h0i2.symm, getLsbD_flipBit_ne x j0 i3 h0i3.symm]
  · intro x
    rw [hdef (flipBit x j1), hdef x,
        getLsbD_flipBit_ne x j1 i0 h1i0.symm, getLsbD_flipBit_ne x j1 i1 h1i1.symm,
        getLsbD_flipBit_ne x j1 i2 h1i2.symm, getLsbD_flipBit_ne x j1 i3 h1i3.symm]
  · intro x
    rw [hdef (flipBit x j2), hdef x,
        getLsbD_flipBit_ne x j2 i0 h2i0.symm, getLsbD_flipBit_ne x j2 i1 h2i1.symm,
        getLsbD_flipBit_ne x j2 i2 h2i2.symm, getLsbD_flipBit_ne x j2 i3 h2i3.symm]
  · intro x
    rw [hdef (flipBit x j3), hdef x,
        getLsbD_flipBit_ne x j3 i0 h3i0.symm, getLsbD_flipBit_ne x j3 i1 h3i1.symm,
        getLsbD_flipBit_ne x j3 i2 h3i2.symm, getLsbD_flipBit_ne x j3 i3 h3i3.symm]

/-- Weight of a single wire or negated wire on `BitVec 3` is `4`. -/
theorem weight_wire3_eq_four (i : Fin 3) :
    weight (fun x : BitVec 3 => x.getLsbD i.val) = 4 ∧
    weight (fun x : BitVec 3 => !x.getLsbD i.val) = 4 := by
  revert i; decide

/-- Weight of a conjunction of two distinct wires (with polarities) on `BitVec 3` is `2`. -/
theorem weight_two_wires3_eq_two (i j : Fin 3) (h : i ≠ j) (bi bj : Bool) :
    weight (fun x : BitVec 3 => (x.getLsbD i.val == bi) && (x.getLsbD j.val == bj)) = 2 := by
  revert i j h bi bj; decide

/-- Weight of a conjunction of two distinct wires (with polarities) on `BitVec 5` is `8`. -/
theorem weight_two_wires5_eq_eight (i j : Fin 5) (h : i ≠ j) (bi bj : Bool) :
    weight (fun x : BitVec 5 => (x.getLsbD i.val == bi) && (x.getLsbD j.val == bj)) = 8 := by
  revert i j h bi bj; decide

end Sparse24E2M1Lop3
