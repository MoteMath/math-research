/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sparse24E2M1Lop3.Core

/-!
# Verified Proofs for Wave 1C Sub-Byte & 2:4-Sparse `LOP3` Circuits

All six headline theorems proved in pure Lean 4 `Init` (zero Mathlib, zero `sorry`,
zero `native_decide`, zero `lemma`).
-/

namespace Sparse24E2M1Lop3

/-! ## Theorem 1: 10-`LOP3` `5t8b → 5 × E2M1` & General `≥ 5`-Variable Lower Bound -/

private def tritOfFin3 (t : Fin 3) : Int :=
  match t with
  | ⟨0, _⟩ => -1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1

private theorem tritOfFin3_isTrit (t : Fin 3) : IsTrit (tritOfFin3 t) := by
  match t with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr (Or.inl rfl)
  | ⟨2, _⟩ => exact Or.inr (Or.inr rfl)

private theorem tritOfFin3_inj {a b : Fin 3} (h : tritOfFin3 a = tritOfFin3 b) : a = b := by
  revert a b h; decide

private theorem unpack5t8b_fin3_exact :
    ∀ t0 t1 t2 t3 t4 : Fin 3,
      decode5E2M1 (unpack5t8b (encode5t8b (tritOfFin3 t0) (tritOfFin3 t1)
        (tritOfFin3 t2) (tritOfFin3 t3) (tritOfFin3 t4))) =
      (2 * tritOfFin3 t0, 2 * tritOfFin3 t1, 2 * tritOfFin3 t2,
       2 * tritOfFin3 t3, 2 * tritOfFin3 t4) := by
  decide

private theorem isTrit_eq_tritOfFin3 {w : Int} (hw : IsTrit w) :
    ∃ t : Fin 3, tritOfFin3 t = w := by
  rcases hw with rfl | rfl | rfl
  · exact ⟨⟨0, by omega⟩, rfl⟩
  · exact ⟨⟨1, by omega⟩, rfl⟩
  · exact ⟨⟨2, by omega⟩, rfl⟩

/-- Insert a value `v` at slot `i : Fin 5` into a 4-tuple `(a, b, c, d)`. -/
private def insert5 (i : Fin 5) (v a b c d : Int) : Int × Int × Int × Int × Int :=
  match i with
  | ⟨0, _⟩ => (v, a, b, c, d)
  | ⟨1, _⟩ => (a, v, b, c, d)
  | ⟨2, _⟩ => (a, b, v, c, d)
  | ⟨3, _⟩ => (a, b, c, v, d)
  | ⟨4, _⟩ => (a, b, c, d, v)

private theorem insert5_inj (i : Fin 5) {v1 a1 b1 c1 d1 v2 a2 b2 c2 d2 : Int}
    (h : insert5 i v1 a1 b1 c1 d1 = insert5 i v2 a2 b2 c2 d2) :
    v1 = v2 ∧ a1 = a2 ∧ b1 = b2 ∧ c1 = c2 ∧ d1 = d2 := by
  match i with
  | ⟨0, _⟩ => simp only [insert5, Prod.mk.injEq] at h; exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  | ⟨1, _⟩ => simp only [insert5, Prod.mk.injEq] at h; exact ⟨h.2.1, h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  | ⟨2, _⟩ => simp only [insert5, Prod.mk.injEq] at h; exact ⟨h.2.2.1, h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩
  | ⟨3, _⟩ => simp only [insert5, Prod.mk.injEq] at h; exact ⟨h.2.2.2.1, h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩
  | ⟨4, _⟩ => simp only [insert5, Prod.mk.injEq] at h; exact ⟨h.2.2.2.2, h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

private theorem slot5_decode5E2M1 (i : Fin 5)
    (t : BitVec 4 × BitVec 4 × BitVec 4 × BitVec 4 × BitVec 4)
    (v a b c d : Int)
    (h : decode5E2M1 t = insert5 i v a b c d) :
    e2m1TwiceVal (slot5 i t) = v := by
  match i with
  | ⟨0, _⟩ => simp only [decode5E2M1, insert5, Prod.mk.injEq] at h; exact h.1
  | ⟨1, _⟩ => simp only [decode5E2M1, insert5, Prod.mk.injEq] at h; exact h.2.1
  | ⟨2, _⟩ => simp only [decode5E2M1, insert5, Prod.mk.injEq] at h; exact h.2.2.1
  | ⟨3, _⟩ => simp only [decode5E2M1, insert5, Prod.mk.injEq] at h; exact h.2.2.2.1
  | ⟨4, _⟩ => simp only [decode5E2M1, insert5, Prod.mk.injEq] at h; exact h.2.2.2.2

private def nzTarget5 (i : Fin 5) (idx : Fin 162) : Int × Int × Int × Int × Int :=
  let v : Int := if idx.val % 2 == 0 then -2 else 2
  let q := idx.val / 2
  let a := 2 * tritOfFin3 ⟨q % 3, by omega⟩
  let b := 2 * tritOfFin3 ⟨(q / 3) % 3, by omega⟩
  let c := 2 * tritOfFin3 ⟨(q / 9) % 3, by omega⟩
  let d := 2 * tritOfFin3 ⟨(q / 27) % 3, by omega⟩
  insert5 i v a b c d

private def zTarget5 (i : Fin 5) (idx : Fin 81) : Int × Int × Int × Int × Int :=
  let q := idx.val
  let a := 2 * tritOfFin3 ⟨q % 3, by omega⟩
  let b := 2 * tritOfFin3 ⟨(q / 3) % 3, by omega⟩
  let c := 2 * tritOfFin3 ⟨(q / 9) % 3, by omega⟩
  let d := 2 * tritOfFin3 ⟨(q / 27) % 3, by omega⟩
  insert5 i 0 a b c d

private theorem tritOfFin3_twice_inj {a b : Fin 3} (h : 2 * tritOfFin3 a = 2 * tritOfFin3 b) :
    a = b :=
  tritOfFin3_inj (by omega)

private theorem nzTarget5_inj (i : Fin 5) (x y : Fin 162)
    (h : nzTarget5 i x = nzTarget5 i y) : x = y := by
  unfold nzTarget5 at h
  rcases insert5_inj i h with ⟨hv, ha, hb, hc, hd⟩
  have hm : x.val % 2 = y.val % 2 := by
    by_cases hx : x.val % 2 = 0 <;> by_cases hy : y.val % 2 = 0 <;> simp_all <;> omega
  have h0 : x.val / 2 % 3 = y.val / 2 % 3 :=
    congrArg Fin.val (tritOfFin3_twice_inj ha)
  have h1 : x.val / 2 / 3 % 3 = y.val / 2 / 3 % 3 :=
    congrArg Fin.val (tritOfFin3_twice_inj hb)
  have h2 : x.val / 2 / 9 % 3 = y.val / 2 / 9 % 3 :=
    congrArg Fin.val (tritOfFin3_twice_inj hc)
  have h3 : x.val / 2 / 27 % 3 = y.val / 2 / 27 % 3 :=
    congrArg Fin.val (tritOfFin3_twice_inj hd)
  apply Fin.ext
  omega

private theorem zTarget5_inj (i : Fin 5) (x y : Fin 81)
    (h : zTarget5 i x = zTarget5 i y) : x = y := by
  unfold zTarget5 at h
  rcases insert5_inj i h with ⟨_, ha, hb, hc, hd⟩
  have h0 : x.val % 3 = y.val % 3 := congrArg Fin.val (tritOfFin3_twice_inj ha)
  have h1 : x.val / 3 % 3 = y.val / 3 % 3 := congrArg Fin.val (tritOfFin3_twice_inj hb)
  have h2 : x.val / 9 % 3 = y.val / 9 % 3 := congrArg Fin.val (tritOfFin3_twice_inj hc)
  have h3 : x.val / 27 % 3 = y.val / 27 % 3 := congrArg Fin.val (tritOfFin3_twice_inj hd)
  apply Fin.ext
  omega

private theorem surj_insert5
    (dec : BitVec 8 → BitVec 4 × BitVec 4 × BitVec 4 × BitVec 4 × BitVec 4)
    (hsurj : ∀ w0 w1 w2 w3 w4 : Int,
      IsTrit w0 → IsTrit w1 → IsTrit w2 → IsTrit w3 → IsTrit w4 →
      ∃ x : BitVec 8, decode5E2M1 (dec x) = (2 * w0, 2 * w1, 2 * w2, 2 * w3, 2 * w4))
    (i : Fin 5) (v a b c d : Int)
    (hv : IsTrit v) (ha : IsTrit a) (hb : IsTrit b) (hc : IsTrit c) (hd : IsTrit d) :
    ∃ x : BitVec 8, decode5E2M1 (dec x) = insert5 i (2 * v) (2 * a) (2 * b) (2 * c) (2 * d) := by
  match i with
  | ⟨0, _⟩ => exact hsurj v a b c d hv ha hb hc hd
  | ⟨1, _⟩ => exact hsurj a v b c d ha hv hb hc hd
  | ⟨2, _⟩ => exact hsurj a b v c d ha hb hv hc hd
  | ⟨3, _⟩ => exact hsurj a b c v d ha hb hc hv hd
  | ⟨4, _⟩ => exact hsurj a b c d v ha hb hc hd hv

theorem unpack_5t8b_to_e2m1_ten_lop3_and_lower_bound :
    (∀ w0 w1 w2 w3 w4 : Int,
      IsTrit w0 → IsTrit w1 → IsTrit w2 → IsTrit w3 → IsTrit w4 →
      decode5E2M1 (unpack5t8b (encode5t8b w0 w1 w2 w3 w4)) =
        (2 * w0, 2 * w1, 2 * w2, 2 * w3, 2 * w4)) ∧
    (∀ (dec : BitVec 8 → BitVec 4 × BitVec 4 × BitVec 4 × BitVec 4 × BitVec 4),
      (∀ w0 w1 w2 w3 w4 : Int,
        IsTrit w0 → IsTrit w1 → IsTrit w2 → IsTrit w3 → IsTrit w4 →
        ∃ x : BitVec 8, decode5E2M1 (dec x) = (2 * w0, 2 * w1, 2 * w2, 2 * w3, 2 * w4)) →
      (∀ i : Fin 5,
        let fi : BitVec 8 → Bool := fun x => e2m1TwiceVal (slot5 i (dec x)) != 0
        162 ≤ weight fi ∧ weight fi ≤ 175) ∧
      (∀ g : BitVec 8 → Bool, DependsOnAtMost4 g → weight g % 16 = 0) ∧
      (∀ i : Fin 5, ¬ DependsOnAtMost4 (fun x => e2m1TwiceVal (slot5 i (dec x)) != 0))) := by
  refine ⟨?_, ?_⟩
  · intro w0 w1 w2 w3 w4 hw0 hw1 hw2 hw3 hw4
    rcases isTrit_eq_tritOfFin3 hw0 with ⟨t0, rfl⟩
    rcases isTrit_eq_tritOfFin3 hw1 with ⟨t1, rfl⟩
    rcases isTrit_eq_tritOfFin3 hw2 with ⟨t2, rfl⟩
    rcases isTrit_eq_tritOfFin3 hw3 with ⟨t3, rfl⟩
    rcases isTrit_eq_tritOfFin3 hw4 with ⟨t4, rfl⟩
    exact unpack5t8b_fin3_exact t0 t1 t2 t3 t4
  · intro dec hsurj
    have hbounds : ∀ i : Fin 5,
        let fi : BitVec 8 → Bool := fun x => e2m1TwiceVal (slot5 i (dec x)) != 0
        162 ≤ weight fi ∧ weight fi ≤ 175 := by
      intro i
      dsimp only
      let fi : BitVec 8 → Bool := fun x => e2m1TwiceVal (slot5 i (dec x)) != 0
      change 162 ≤ weight fi ∧ weight fi ≤ 175
      have hge : 162 ≤ weight fi := by
        apply le_weight_of_exists fi (fun x => decode5E2M1 (dec x)) (nzTarget5 i) (nzTarget5_inj i)
        · intro idx
          unfold nzTarget5
          have hv : IsTrit (if idx.val % 2 == 0 then (-1 : Int) else 1) := by
            by_cases h : idx.val % 2 = 0 <;> simp [h, IsTrit]
          have hmul : (if idx.val % 2 == 0 then (-2 : Int) else 2) =
              2 * (if idx.val % 2 == 0 then (-1 : Int) else 1) := by
            by_cases h : idx.val % 2 = 0 <;> simp [h]
          rw [hmul]
          exact surj_insert5 dec hsurj i _ _ _ _ _ hv
            (tritOfFin3_isTrit _) (tritOfFin3_isTrit _) (tritOfFin3_isTrit _) (tritOfFin3_isTrit _)
        · intro x idx hx
          unfold nzTarget5 at hx
          have hs := slot5_decode5E2M1 i (dec x) _ _ _ _ _ hx
          simp only [fi, hs]
          by_cases h : idx.val % 2 = 0 <;> simp [h]
      have hnot_ge : 81 ≤ weight (fun x => !fi x) := by
        apply le_weight_of_exists (fun x => !fi x) (fun x => decode5E2M1 (dec x))
          (zTarget5 i) (zTarget5_inj i)
        · intro idx
          unfold zTarget5
          have h0 : (0 : Int) = 2 * 0 := rfl
          rw [h0]
          exact surj_insert5 dec hsurj i 0 _ _ _ _ (Or.inr (Or.inl rfl))
            (tritOfFin3_isTrit _) (tritOfFin3_isTrit _) (tritOfFin3_isTrit _) (tritOfFin3_isTrit _)
        · intro x idx hx
          unfold zTarget5 at hx
          have hs := slot5_decode5E2M1 i (dec x) _ _ _ _ _ hx
          simp [fi, hs]
      have hsum := weight_add_not fi
      have h256 : (2 : Nat) ^ 8 = 256 := rfl
      exact ⟨hge, by omega⟩
    refine ⟨hbounds, weight_mod_sixteen_of_dependsOnAtMost4, ?_⟩
    intro i hdep
    have hb := hbounds i
    have hmod := weight_mod_sixteen_of_dependsOnAtMost4 _ hdep
    omega

/-! ## Theorem 2: Tight 1-`LOP3` `3b → 4b 2:4 Mask` & `3b → Unordered {idx0, idx1}` -/

private theorem unpackMask24_3b_bij :
    ∀ m : BitVec 4, isMask24 m = true →
      ∃ x : BitVec 3, unpackMask24_3b x = m ∧ ∀ y : BitVec 3, unpackMask24_3b y = m → y = x := by
  decide

private theorem unpackUnordered24_3b_ne :
    ∀ x : BitVec 3, (unpackUnordered24_3b x).1 ≠ (unpackUnordered24_3b x).2 := by
  decide

private theorem unpackUnordered24_3b_exact :
    ∀ a b : Fin 4, a < b →
      let (u, v) := unpackUnordered24_3b (encodeUnordered24_3b a b)
      u ≠ v ∧ ((u = a ∧ v = b) ∨ (u = b ∧ v = a)) := by
  decide

private theorem mask24_bit_not_const (b : Fin 4) (c : Bool) :
    ∃ m : BitVec 4, isMask24 m = true ∧ m.getLsbD b.val ≠ c := by
  revert b c; decide

private theorem mask24_two_bits_all_pairs (b1 b2 : Fin 4) (h : b1 ≠ b2) (v1 v2 : Bool) :
    ∃ m : BitVec 4, isMask24 m = true ∧ m.getLsbD b1.val = v1 ∧ m.getLsbD b2.val = v2 := by
  revert b1 b2 h v1 v2; decide

private theorem fin4_to_fin3_pigeonhole (f : Fin 4 → Fin 3) :
    ∃ b1 b2 : Fin 4, b1 ≠ b2 ∧ f b1 = f b2 := by
  have h : ∀ a0 a1 a2 a3 : Fin 3,
      a0 = a1 ∨ a0 = a2 ∨ a0 = a3 ∨ a1 = a2 ∨ a1 = a3 ∨ a2 = a3 := by decide
  rcases h (f 0) (f 1) (f 2) (f 3) with h01 | h02 | h03 | h12 | h13 | h23
  · exact ⟨0, 1, by decide, h01⟩
  · exact ⟨0, 2, by decide, h02⟩
  · exact ⟨0, 3, by decide, h03⟩
  · exact ⟨1, 2, by decide, h12⟩
  · exact ⟨1, 3, by decide, h13⟩
  · exact ⟨2, 3, by decide, h23⟩

theorem sparse24_3bit_single_lop3_tight :
    (∀ m : BitVec 4, isMask24 m = true →
      ∃ x : BitVec 3, unpackMask24_3b x = m ∧ ∀ y : BitVec 3, unpackMask24_3b y = m → y = x) ∧
    (∀ dec : BitVec 3 → BitVec 4,
      (∀ m : BitVec 4, isMask24 m = true → ∃ x : BitVec 3, dec x = m) →
      ¬ (∀ b : Fin 4, WireOrConst (fun x : BitVec 3 => (dec x).getLsbD b.val))) ∧
    (∀ x : BitVec 3, (unpackUnordered24_3b x).1 ≠ (unpackUnordered24_3b x).2) ∧
    (∀ a b : Fin 4, a < b →
      let (u, v) := unpackUnordered24_3b (encodeUnordered24_3b a b)
      u ≠ v ∧ ((u = a ∧ v = b) ∨ (u = b ∧ v = a))) := by
  refine ⟨unpackMask24_3b_bij, ?_, unpackUnordered24_3b_ne, unpackUnordered24_3b_exact⟩
  intro dec hsurj hwire
  have hnonconst : ∀ b : Fin 4, ∃ i : Fin 3,
      (∀ x : BitVec 3, (dec x).getLsbD b.val = x.getLsbD i.val) ∨
      (∀ x : BitVec 3, (dec x).getLsbD b.val = !x.getLsbD i.val) := by
    intro b
    rcases hwire b with ⟨c, hc⟩ | hw
    · rcases mask24_bit_not_const b c with ⟨m, hm, hne⟩
      rcases hsurj m hm with ⟨x, hx⟩
      have h1 : (dec x).getLsbD b.val = c := hc x
      rw [hx] at h1
      exact absurd h1 hne
    · exact hw
  let wireIdx : Fin 4 → Fin 3 := fun b => Classical.choose (hnonconst b)
  have hspec : ∀ b : Fin 4,
      (∀ x : BitVec 3, (dec x).getLsbD b.val = x.getLsbD (wireIdx b).val) ∨
      (∀ x : BitVec 3, (dec x).getLsbD b.val = !x.getLsbD (wireIdx b).val) :=
    fun b => Classical.choose_spec (hnonconst b)
  rcases fin4_to_fin3_pigeonhole wireIdx with ⟨b1, b2, hne, heq⟩
  rcases hspec b1 with h1 | h1 <;> rcases hspec b2 with h2 | h2
  · rcases mask24_two_bits_all_pairs b1 b2 hne false true with ⟨m, hm, hm1, hm2⟩
    rcases hsurj m hm with ⟨x, hx⟩
    have e1 := h1 x; have e2 := h2 x
    rw [hx, hm1] at e1; rw [hx, hm2, ← heq] at e2
    rw [← e1] at e2; exact Bool.noConfusion e2
  · rcases mask24_two_bits_all_pairs b1 b2 hne false false with ⟨m, hm, hm1, hm2⟩
    rcases hsurj m hm with ⟨x, hx⟩
    have e1 := h1 x; have e2 := h2 x
    rw [hx, hm1] at e1; rw [hx, hm2, ← heq] at e2
    rw [← e1] at e2; exact Bool.noConfusion e2
  · rcases mask24_two_bits_all_pairs b1 b2 hne false false with ⟨m, hm, hm1, hm2⟩
    rcases hsurj m hm with ⟨x, hx⟩
    have e1 := h1 x; have e2 := h2 x
    rw [hx, hm1] at e1; rw [hx, hm2, ← heq] at e2
    rw [← e2] at e1; exact Bool.noConfusion e1
  · rcases mask24_two_bits_all_pairs b1 b2 hne false true with ⟨m, hm, hm1, hm2⟩
    rcases hsurj m hm with ⟨x, hx⟩
    have e1 := h1 x; have e2 := h2 x
    rw [hx, hm1] at e1; rw [hx, hm2, ← heq] at e2
    rw [← e1] at e2; exact Bool.noConfusion e2

/-! ## Theorem 3: Tight 3-`LOP3` `3b → Ordered (idx0 < idx1)` -/

private theorem unpackOrdered24_3b_bij :
    ∀ a b : Fin 4, a < b →
      unpackOrdered24_3b (encodeOrdered24_3b a b) = (a, b) ∧
      ∀ y : BitVec 3, unpackOrdered24_3b y = (a, b) → y = encodeOrdered24_3b a b := by
  decide

private def ordPair5_i01_false (k : Fin 5) : Fin 4 × Fin 4 :=
  match k with
  | ⟨0, _⟩ => (0, 1)
  | ⟨1, _⟩ => (0, 2)
  | ⟨2, _⟩ => (0, 3)
  | ⟨3, _⟩ => (1, 2)
  | ⟨4, _⟩ => (1, 3)

private def ordPair5_i11_true (k : Fin 5) : Fin 4 × Fin 4 :=
  match k with
  | ⟨0, _⟩ => (0, 2)
  | ⟨1, _⟩ => (0, 3)
  | ⟨2, _⟩ => (1, 2)
  | ⟨3, _⟩ => (1, 3)
  | ⟨4, _⟩ => (2, 3)

private def ordPair3_01 (k : Fin 3) : Fin 4 × Fin 4 :=
  match k with
  | ⟨0, _⟩ => (0, 1)
  | ⟨1, _⟩ => (0, 3)
  | ⟨2, _⟩ => (2, 3)

private theorem wireOrConst3_weight_cases (f : BitVec 3 → Bool) (hf : WireOrConst f) :
    weight f = 0 ∨ weight f = 4 ∨ weight f = 8 := by
  rcases hf with ⟨c, hc⟩ | ⟨i, hi | hi⟩
  · have hfeq : f = fun _ => c := funext hc
    subst hfeq
    cases c
    · left; decide
    · right; right; decide
  · have hfeq : f = fun x => x.getLsbD i.val := funext hi
    subst hfeq
    right; left; exact (weight_wire3_eq_four i).1
  · have hfeq : f = fun x => !x.getLsbD i.val := funext hi
    subst hfeq
    right; left; exact (weight_wire3_eq_four i).2

theorem sparse24_3bit_ordered_three_lop3_tight :
    (∀ a b : Fin 4, a < b →
      unpackOrdered24_3b (encodeOrdered24_3b a b) = (a, b) ∧
      ∀ y : BitVec 3, unpackOrdered24_3b y = (a, b) → y = encodeOrdered24_3b a b) ∧
    (∀ dec : BitVec 3 → Fin 4 × Fin 4,
      (∀ a b : Fin 4, a < b → ∃ x : BitVec 3, dec x = (a, b)) →
      ∀ k1 k2 : Fin 4, k1 ≠ k2 →
        ¬ (WireOrConst (fun x => idxPairBit (dec x) k1) ∧
           WireOrConst (fun x => idxPairBit (dec x) k2))) := by
  refine ⟨unpackOrdered24_3b_bij, ?_⟩
  intro dec hsurj
  -- Bit 1 (i0_1) cannot be WireOrConst: weight ∈ [1, 3]
  have hnot1 : ¬ WireOrConst (fun x => idxPairBit (dec x) 1) := by
    intro hw
    let f : BitVec 3 → Bool := fun x => idxPairBit (dec x) 1
    have hge1 : 1 ≤ weight f := by
      rcases hsurj 2 3 (by decide) with ⟨x, hx⟩
      apply le_weight_of_inj f (fun _ : Fin 1 => x) (fun a b _ => Subsingleton.elim a b)
      intro _; simp [f, hx, idxPairBit]
    have hnot5 : 5 ≤ weight (fun x => !f x) := by
      apply le_weight_of_exists (fun x => !f x) dec ordPair5_i01_false
      · decide
      · intro a
        have hlt : (ordPair5_i01_false a).1 < (ordPair5_i01_false a).2 := by revert a; decide
        exact hsurj _ _ hlt
      · intro x a hx
        simp only [f, hx]
        clear hx; revert a; decide
    have hsum := weight_add_not f
    have hcases := wireOrConst3_weight_cases f hw
    have h8 : (2 : Nat) ^ 3 = 8 := rfl
    omega
  -- Bit 3 (i1_1) cannot be WireOrConst: weight ∈ [5, 7]
  have hnot3 : ¬ WireOrConst (fun x => idxPairBit (dec x) 3) := by
    intro hw
    let f : BitVec 3 → Bool := fun x => idxPairBit (dec x) 3
    have hge5 : 5 ≤ weight f := by
      apply le_weight_of_exists f dec ordPair5_i11_true
      · decide
      · intro a
        have hlt : (ordPair5_i11_true a).1 < (ordPair5_i11_true a).2 := by revert a; decide
        exact hsurj _ _ hlt
      · intro x a hx
        simp only [f, hx]
        clear hx; revert a; decide
    have hnot1 : 1 ≤ weight (fun x => !f x) := by
      rcases hsurj 0 1 (by decide) with ⟨x, hx⟩
      apply le_weight_of_inj (fun x => !f x) (fun _ : Fin 1 => x) (fun a b _ => Subsingleton.elim a b)
      intro _; simp [f, hx, idxPairBit]
    have hsum := weight_add_not f
    have hcases := wireOrConst3_weight_cases f hw
    have h8 : (2 : Nat) ^ 3 = 8 := rfl
    omega
  -- Bits 0 (i0_0) and 2 (i1_0) cannot BOTH be WireOrConst
  have hnot02 : ¬ (WireOrConst (fun x => idxPairBit (dec x) 0) ∧
                   WireOrConst (fun x => idxPairBit (dec x) 2)) := by
    rintro ⟨hw0, hw2⟩
    have h0_wire : ∃ i : Fin 3, ∃ b0 : Bool,
        ∀ x : BitVec 3, idxPairBit (dec x) 0 = (x.getLsbD i.val == b0) := by
      rcases hw0 with ⟨c, hc⟩ | ⟨i, hi | hi⟩
      · cases c
        · rcases hsurj 1 2 (by decide) with ⟨x, hx⟩
          have h : idxPairBit (dec x) 0 = false := hc x
          rw [hx] at h; simp [idxPairBit] at h
        · rcases hsurj 0 1 (by decide) with ⟨x, hx⟩
          have h : idxPairBit (dec x) 0 = true := hc x
          rw [hx] at h; simp [idxPairBit] at h
      · exact ⟨i, true, fun x => by have h : idxPairBit (dec x) 0 = x.getLsbD i.val := hi x; rw [h]; cases x.getLsbD i.val <;> rfl⟩
      · exact ⟨i, false, fun x => by have h : idxPairBit (dec x) 0 = !x.getLsbD i.val := hi x; rw [h]; cases x.getLsbD i.val <;> rfl⟩
    have h2_wire : ∃ j : Fin 3, ∃ b2 : Bool,
        ∀ x : BitVec 3, idxPairBit (dec x) 2 = (x.getLsbD j.val == b2) := by
      rcases hw2 with ⟨c, hc⟩ | ⟨j, hj | hj⟩
      · cases c
        · rcases hsurj 0 1 (by decide) with ⟨x, hx⟩
          have h : idxPairBit (dec x) 2 = false := hc x
          rw [hx] at h; simp [idxPairBit] at h
        · rcases hsurj 0 2 (by decide) with ⟨x, hx⟩
          have h : idxPairBit (dec x) 2 = true := hc x
          rw [hx] at h; simp [idxPairBit] at h
      · exact ⟨j, true, fun x => by have h : idxPairBit (dec x) 2 = x.getLsbD j.val := hj x; rw [h]; cases x.getLsbD j.val <;> rfl⟩
      · exact ⟨j, false, fun x => by have h : idxPairBit (dec x) 2 = !x.getLsbD j.val := hj x; rw [h]; cases x.getLsbD j.val <;> rfl⟩
    rcases h0_wire with ⟨i, b0, hi⟩
    rcases h2_wire with ⟨j, b2, hj⟩
    by_cases hij : i = j
    · subst hij
      by_cases hbb : b0 = b2
      · subst hbb
        rcases hsurj 0 1 (by decide) with ⟨x, hx⟩
        have e0 := hi x; have e2 := hj x
        rw [hx] at e0 e2
        simp only [idxPairBit] at e0 e2
        rw [← e0] at e2; cases e2
      · rcases hsurj 0 2 (by decide) with ⟨x, hx⟩
        have e0 := hi x; have e2 := hj x
        rw [hx] at e0 e2
        simp only [idxPairBit] at e0 e2
        cases b0 <;> cases b2 <;> cases x.getLsbD i.val <;> simp_all
    · let f01 : BitVec 3 → Bool := fun x =>
        (!idxPairBit (dec x) 0) && (idxPairBit (dec x) 2)
      have hge3 : 3 ≤ weight f01 := by
        apply le_weight_of_exists f01 dec ordPair3_01
        · decide
        · intro a
          have hlt : (ordPair3_01 a).1 < (ordPair3_01 a).2 := by revert a; decide
          exact hsurj _ _ hlt
        · intro x a hx
          simp only [f01, hx]
          clear hx; revert a; decide
      have hfeq : f01 = fun x : BitVec 3 =>
          (x.getLsbD i.val == !b0) && (x.getLsbD j.val == b2) := by
        funext x
        simp only [f01, hi x, hj x]
        cases x.getLsbD i.val <;> cases b0 <;> rfl
      rw [hfeq, weight_two_wires3_eq_two i j hij (!b0) b2] at hge3
      omega
  intro k1 k2 hne ⟨hw1, hw2⟩
  have hfin4 : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
  rcases hfin4 k1 with rfl | rfl | rfl | rfl
  · rcases hfin4 k2 with rfl | rfl | rfl | rfl
    · exact hne rfl
    · exact hnot1 hw2
    · exact hnot02 ⟨hw1, hw2⟩
    · exact hnot3 hw2
  · exact hnot1 hw1
  · rcases hfin4 k2 with rfl | rfl | rfl | rfl
    · exact hnot02 ⟨hw2, hw1⟩
    · exact hnot1 hw2
    · exact hne rfl
    · exact hnot3 hw2
  · exact hnot3 hw1

/-! ## Theorem 4: 12-`LOP3` `8b → 3 × 4b 2:4 Masks` & Fiber-Product Direct-Wire Bound -/

private def validMask24 (i : Fin 6) : BitVec 4 :=
  match i with
  | ⟨0, _⟩ => BitVec.ofNat 4 3
  | ⟨1, _⟩ => BitVec.ofNat 4 5
  | ⟨2, _⟩ => BitVec.ofNat 4 6
  | ⟨3, _⟩ => BitVec.ofNat 4 9
  | ⟨4, _⟩ => BitVec.ofNat 4 10
  | ⟨5, _⟩ => BitVec.ofNat 4 12

private theorem isMask24_eq_validMask24 (m : BitVec 4) (hm : isMask24 m = true) :
    ∃ i : Fin 6, validMask24 i = m := by
  revert m hm; decide

private theorem unpackTripleMask24_8b_fin6_exact :
    ∀ i0 i1 i2 : Fin 6,
      unpackTripleMask24_8b
        (encodeTripleMask24_8b (validMask24 i0) (validMask24 i1) (validMask24 i2)) =
      (validMask24 i0, validMask24 i1, validMask24 i2) := by
  decide

private theorem fiber_product_unique_111_fin4 :
    ∀ d0 d1 d2 : Fin 4,
      d0.val + d1.val + d2.val ≤ 8 →
      maxFiber d0.val * maxFiber d1.val * maxFiber d2.val ≤
        2 ^ (8 - (d0.val + d1.val + d2.val)) →
      d0.val + d1.val + d2.val ≥ 3 →
      d0.val + d1.val + d2.val = 3 ∧ d0.val = 1 ∧ d1.val = 1 ∧ d2.val = 1 := by
  decide

theorem sparse24_8bit_triple_twelve_lop3_and_wire_bound :
    (∀ m0 m1 m2 : BitVec 4,
      isMask24 m0 = true → isMask24 m1 = true → isMask24 m2 = true →
      unpackTripleMask24_8b (encodeTripleMask24_8b m0 m1 m2) = (m0, m1, m2)) ∧
    (∀ d0 d1 d2 : Nat, d0 ≤ 3 → d1 ≤ 3 → d2 ≤ 3 → d0 + d1 + d2 ≤ 8 →
      maxFiber d0 * maxFiber d1 * maxFiber d2 ≤ 2 ^ (8 - (d0 + d1 + d2)) →
      d0 + d1 + d2 ≥ 3 →
      d0 + d1 + d2 = 3 ∧ d0 = 1 ∧ d1 = 1 ∧ d2 = 1) := by
  refine ⟨?_, ?_⟩
  · intro m0 m1 m2 h0 h1 h2
    rcases isMask24_eq_validMask24 m0 h0 with ⟨i0, rfl⟩
    rcases isMask24_eq_validMask24 m1 h1 with ⟨i1, rfl⟩
    rcases isMask24_eq_validMask24 m2 h2 with ⟨i2, rfl⟩
    exact unpackTripleMask24_8b_fin6_exact i0 i1 i2
  · intro d0 d1 d2 h0 h1 h2 hle8 hfib hge
    exact fiber_product_unique_111_fin4 ⟨d0, by omega⟩ ⟨d1, by omega⟩ ⟨d2, by omega⟩ hle8 hfib hge

/-! ## Theorem 5: 25-`LOP3` Zero-FP `E2M1 × E2M1` Magnitude Multiplier -/

theorem e2m1_mag_mul_25lop3_exact :
    ∀ a b : BitVec 3, (e2m1MagMul25 a b).toNat = e2m1MagVal a * e2m1MagVal b := by
  decide

/-! ## Theorem 6: 4-`LOP3` Depth-2 `2q5b → 2 × E2M1` & 4-Wire Impossibility -/

private def quinOfFin5 (q : Fin 5) : Int :=
  match q with
  | ⟨0, _⟩ => -2
  | ⟨1, _⟩ => -1
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 2

private theorem quinOfFin5_isQuinary (q : Fin 5) : IsQuinary (quinOfFin5 q) := by
  match q with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr (Or.inl rfl)
  | ⟨2, _⟩ => exact Or.inr (Or.inr (Or.inl rfl))
  | ⟨3, _⟩ => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | ⟨4, _⟩ => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

private theorem quinOfFin5_twice_inj {a b : Fin 5}
    (h : 2 * quinOfFin5 a = 2 * quinOfFin5 b) : a = b := by
  revert a b h; decide

private theorem isQuinary_eq_quinOfFin5 {w : Int} (hw : IsQuinary w) :
    ∃ q : Fin 5, quinOfFin5 q = w := by
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨0, by omega⟩, rfl⟩
  · exact ⟨⟨1, by omega⟩, rfl⟩
  · exact ⟨⟨2, by omega⟩, rfl⟩
  · exact ⟨⟨3, by omega⟩, rfl⟩
  · exact ⟨⟨4, by omega⟩, rfl⟩

private theorem unpack2q5b_fin5_exact :
    ∀ q0 q1 : Fin 5,
      let (n0, n1) := unpack2q5b (encode2q5b (quinOfFin5 q0) (quinOfFin5 q1))
      e2m1TwiceVal n0 = 2 * quinOfFin5 q0 ∧ e2m1TwiceVal n1 = 2 * quinOfFin5 q1 := by
  decide

private theorem e2m1_quinary_bits_fin5 (n : BitVec 4) (q : Fin 5)
    (h : e2m1TwiceVal n = 2 * quinOfFin5 q) :
    (n.getLsbD 2 = false ∨ n.getLsbD 1 = false) ∧
    (n.getLsbD 2 = true ↔ quinOfFin5 q = -2 ∨ quinOfFin5 q = 2) ∧
    (n.getLsbD 1 = true ↔ quinOfFin5 q = -1 ∨ quinOfFin5 q = 1) := by
  revert n q h
  decide

private theorem e2m1_quinary_bits (n : BitVec 4) (w : Int)
    (hw : IsQuinary w) (h : e2m1TwiceVal n = 2 * w) :
    (n.getLsbD 2 = false ∨ n.getLsbD 1 = false) ∧
    (n.getLsbD 2 = true ↔ w = -2 ∨ w = 2) ∧
    (n.getLsbD 1 = true ↔ w = -1 ∨ w = 1) := by
  rcases isQuinary_eq_quinOfFin5 hw with ⟨q, rfl⟩
  exact e2m1_quinary_bits_fin5 n q h

private theorem quinary_not_const_witness (k : Fin 6) (c : Bool) :
    ∃ q0 q1 : Fin 5, ∀ n0 n1 : BitVec 4,
      e2m1TwiceVal n0 = 2 * quinOfFin5 q0 → e2m1TwiceVal n1 = 2 * quinOfFin5 q1 →
      quinaryOutBit (n0, n1) k ≠ c := by
  revert k c; decide

private theorem quinary_pair_diff_wire
    (dec : BitVec 5 → BitVec 4 × BitVec 4)
    (hsurj : ∀ w0 w1 : Int, IsQuinary w0 → IsQuinary w1 →
      ∃ x : BitVec 5,
        e2m1TwiceVal (dec x).1 = 2 * w0 ∧ e2m1TwiceVal (dec x).2 = 2 * w1)
    (k : Fin 6) (hw : WireOrConst (fun x => quinaryOutBit (dec x) k)) :
    ∃ (i : Fin 5) (b : Bool),
      ∀ x : BitVec 5, quinaryOutBit (dec x) k = (x.getLsbD i.val == b) := by
  rcases hw with ⟨c, hc⟩ | ⟨i, hi | hi⟩
  · rcases quinary_not_const_witness k c with ⟨q0, q1, hne⟩
    rcases hsurj (quinOfFin5 q0) (quinOfFin5 q1) (quinOfFin5_isQuinary q0) (quinOfFin5_isQuinary q1) with
      ⟨x, hx0, hx1⟩
    exact absurd (hc x) (hne (dec x).1 (dec x).2 hx0 hx1)
  · exact ⟨i, true, fun x => by have h : quinaryOutBit (dec x) k = x.getLsbD i.val := hi x; rw [h]; cases x.getLsbD i.val <;> rfl⟩
  · exact ⟨i, false, fun x => by have h : quinaryOutBit (dec x) k = !x.getLsbD i.val := hi x; rw [h]; cases x.getLsbD i.val <;> rfl⟩

/-- No two distinct output bits among `(S0, E1_0, E0_0, S1, E1_1, E0_1)` can be equal or
    complementary on all inputs of a surjective `2q5b → 2 × E2M1` decoder. -/
private theorem quinary_no_shared_wire
    (dec : BitVec 5 → BitVec 4 × BitVec 4)
    (hsurj : ∀ w0 w1 : Int, IsQuinary w0 → IsQuinary w1 →
      ∃ x : BitVec 5,
        e2m1TwiceVal (dec x).1 = 2 * w0 ∧ e2m1TwiceVal (dec x).2 = 2 * w1)
    (ka kb : Fin 6) (hne : ka ≠ kb) (i : Fin 5) (ba bb : Bool)
    (ha : ∀ x : BitVec 5, quinaryOutBit (dec x) ka = (x.getLsbD i.val == ba))
    (hb : ∀ x : BitVec 5, quinaryOutBit (dec x) kb = (x.getLsbD i.val == bb)) :
    False := by
  have hcheck : ∀ (ka kb : Fin 6), ka ≠ kb → ∀ (same : Bool),
      ∃ q0 q1 : Fin 5, ∀ n0 n1 : BitVec 4,
        e2m1TwiceVal n0 = 2 * quinOfFin5 q0 → e2m1TwiceVal n1 = 2 * quinOfFin5 q1 →
        (quinaryOutBit (n0, n1) ka == quinaryOutBit (n0, n1) kb) ≠ same := by
    decide
  rcases hcheck ka kb hne (ba == bb) with ⟨q0, q1, hviol⟩
  rcases hsurj (quinOfFin5 q0) (quinOfFin5 q1) (quinOfFin5_isQuinary q0) (quinOfFin5_isQuinary q1) with
    ⟨x, hx0, hx1⟩
  have h1 := ha x
  have h2 := hb x
  have heq : (quinaryOutBit (dec x) ka == quinaryOutBit (dec x) kb) = (ba == bb) := by
    rw [h1, h2]
    cases x.getLsbD i.val <;> cases ba <;> cases bb <;> rfl
  exact hviol (dec x).1 (dec x).2 hx0 hx1 heq

/-- Case A: `(E1_0, E0_0)` cannot both be wires (leaves `32 - 8 = 24 < 25` valid codes). -/
private theorem quinary_no_both_exp0
    (dec : BitVec 5 → BitVec 4 × BitVec 4)
    (hsurj : ∀ w0 w1 : Int, IsQuinary w0 → IsQuinary w1 →
      ∃ x : BitVec 5,
        e2m1TwiceVal (dec x).1 = 2 * w0 ∧ e2m1TwiceVal (dec x).2 = 2 * w1)
    (h1 : WireOrConst (fun x => quinaryOutBit (dec x) 1))
    (h2 : WireOrConst (fun x => quinaryOutBit (dec x) 2)) : False := by
  rcases quinary_pair_diff_wire dec hsurj 1 h1 with ⟨i1, b1, hi1⟩
  rcases quinary_pair_diff_wire dec hsurj 2 h2 with ⟨i2, b2, hi2⟩
  have hne : i1 ≠ i2 := fun heq => by
    subst heq; exact quinary_no_shared_wire dec hsurj 1 2 (by decide) i1 b1 b2 hi1 hi2
  let bad : BitVec 5 → Bool := fun x => quinaryOutBit (dec x) 1 && quinaryOutBit (dec x) 2
  have hbad_eq : bad = fun x : BitVec 5 =>
      (x.getLsbD i1.val == b1) && (x.getLsbD i2.val == b2) := by
    funext x; simp [bad, hi1 x, hi2 x]
  have hw_bad : weight bad = 8 := by
    rw [hbad_eq]; exact weight_two_wires5_eq_eight i1 i2 hne b1 b2
  have hgood : 25 ≤ weight (fun x => !bad x) := by
    let target : Fin 25 → Int × Int := fun idx =>
      (2 * quinOfFin5 ⟨idx.val % 5, by omega⟩, 2 * quinOfFin5 ⟨idx.val / 5, by omega⟩)
    apply le_weight_of_exists (fun x => !bad x)
      (fun x => (e2m1TwiceVal (dec x).1, e2m1TwiceVal (dec x).2)) target
    · intro a b hab
      simp only [target, Prod.mk.injEq] at hab
      have h0 : a.val % 5 = b.val % 5 := congrArg Fin.val (quinOfFin5_twice_inj hab.1)
      have h1 : a.val / 5 = b.val / 5 := congrArg Fin.val (quinOfFin5_twice_inj hab.2)
      exact Fin.ext (by omega)
    · intro idx
      rcases hsurj _ _ (quinOfFin5_isQuinary ⟨idx.val % 5, by omega⟩)
        (quinOfFin5_isQuinary ⟨idx.val / 5, by omega⟩) with ⟨x, hx0, hx1⟩
      exact ⟨x, Prod.ext hx0 hx1⟩
    · intro x idx hx
      simp only [target, Prod.mk.injEq] at hx
      have hno := (e2m1_quinary_bits (dec x).1 _ (quinOfFin5_isQuinary _) hx.1).1
      rcases hno with hf | hf <;>
        simp only [bad, quinaryOutBit, hf, Bool.false_and, Bool.and_false, Bool.not_false]
  have hsum := weight_add_not bad
  have h32 : (2 : Nat) ^ 5 = 32 := rfl
  omega

/-- Case A': `(E1_1, E0_1)` cannot both be wires (leaves `32 - 8 = 24 < 25` valid codes). -/
private theorem quinary_no_both_exp1
    (dec : BitVec 5 → BitVec 4 × BitVec 4)
    (hsurj : ∀ w0 w1 : Int, IsQuinary w0 → IsQuinary w1 →
      ∃ x : BitVec 5,
        e2m1TwiceVal (dec x).1 = 2 * w0 ∧ e2m1TwiceVal (dec x).2 = 2 * w1)
    (h4 : WireOrConst (fun x => quinaryOutBit (dec x) 4))
    (h5 : WireOrConst (fun x => quinaryOutBit (dec x) 5)) : False := by
  rcases quinary_pair_diff_wire dec hsurj 4 h4 with ⟨i4, b4, hi4⟩
  rcases quinary_pair_diff_wire dec hsurj 5 h5 with ⟨i5, b5, hi5⟩
  have hne : i4 ≠ i5 := fun heq => by
    subst heq; exact quinary_no_shared_wire dec hsurj 4 5 (by decide) i4 b4 b5 hi4 hi5
  let bad : BitVec 5 → Bool := fun x => quinaryOutBit (dec x) 4 && quinaryOutBit (dec x) 5
  have hbad_eq : bad = fun x : BitVec 5 =>
      (x.getLsbD i4.val == b4) && (x.getLsbD i5.val == b5) := by
    funext x; simp [bad, hi4 x, hi5 x]
  have hw_bad : weight bad = 8 := by
    rw [hbad_eq]; exact weight_two_wires5_eq_eight i4 i5 hne b4 b5
  have hgood : 25 ≤ weight (fun x => !bad x) := by
    let target : Fin 25 → Int × Int := fun idx =>
      (2 * quinOfFin5 ⟨idx.val % 5, by omega⟩, 2 * quinOfFin5 ⟨idx.val / 5, by omega⟩)
    apply le_weight_of_exists (fun x => !bad x)
      (fun x => (e2m1TwiceVal (dec x).1, e2m1TwiceVal (dec x).2)) target
    · intro a b hab
      simp only [target, Prod.mk.injEq] at hab
      have h0 : a.val % 5 = b.val % 5 := congrArg Fin.val (quinOfFin5_twice_inj hab.1)
      have h1 : a.val / 5 = b.val / 5 := congrArg Fin.val (quinOfFin5_twice_inj hab.2)
      exact Fin.ext (by omega)
    · intro idx
      rcases hsurj _ _ (quinOfFin5_isQuinary ⟨idx.val % 5, by omega⟩)
        (quinOfFin5_isQuinary ⟨idx.val / 5, by omega⟩) with ⟨x, hx0, hx1⟩
      exact ⟨x, Prod.ext hx0 hx1⟩
    · intro x idx hx
      simp only [target, Prod.mk.injEq] at hx
      have hno := (e2m1_quinary_bits (dec x).2 _ (quinOfFin5_isQuinary _) hx.2).1
      rcases hno with hf | hf <;>
        simp only [bad, quinaryOutBit, hf, Bool.false_and, Bool.and_false, Bool.not_false]
  have hsum := weight_add_not bad
  have h32 : (2 : Nat) ^ 5 = 32 := rfl
  omega

private def expZeroVal (isE1 : Bool) (t : Fin 3) : Int :=
  if isE1 then
    match t with | ⟨0, _⟩ => -1 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 1
  else
    match t with | ⟨0, _⟩ => -2 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 2

private theorem expZeroVal_isQuinary (isE1 : Bool) (t : Fin 3) :
    IsQuinary (expZeroVal isE1 t) := by
  cases isE1 <;> match t with
  | ⟨0, _⟩ => simp [expZeroVal, IsQuinary]
  | ⟨1, _⟩ => simp [expZeroVal, IsQuinary]
  | ⟨2, _⟩ => simp [expZeroVal, IsQuinary]

private theorem expZeroVal_twice_inj (isE1 : Bool) {t1 t2 : Fin 3}
    (h : 2 * expZeroVal isE1 t1 = 2 * expZeroVal isE1 t2) : t1 = t2 := by
  revert isE1 t1 t2 h; decide

private theorem expZeroVal_bit_false (isE1 : Bool) (n : BitVec 4) (t : Fin 3)
    (h : e2m1TwiceVal n = 2 * expZeroVal isE1 t) :
    (if isE1 then n.getLsbD 2 else n.getLsbD 1) = false := by
  revert isE1 n t h; decide

/-- Case B: No pair `(X0, X1)` with `X0 ∈ {E1_0, E0_0}` and `X1 ∈ {E1_1, E0_1}` can both be
    wires (`3 × 3 = 9` quinary pairs have `X0 = X1 = false`, exceeding the fiber size `8`). -/
private theorem quinary_no_cross_exp
    (dec : BitVec 5 → BitVec 4 × BitVec 4)
    (hsurj : ∀ w0 w1 : Int, IsQuinary w0 → IsQuinary w1 →
      ∃ x : BitVec 5,
        e2m1TwiceVal (dec x).1 = 2 * w0 ∧ e2m1TwiceVal (dec x).2 = 2 * w1)
    (ka kb : Fin 6) (hka : ka = 1 ∨ ka = 2) (hkb : kb = 4 ∨ kb = 5)
    (ha : WireOrConst (fun x => quinaryOutBit (dec x) ka))
    (hb : WireOrConst (fun x => quinaryOutBit (dec x) kb)) : False := by
  have hkab : ka ≠ kb := by
    rcases hka with rfl | rfl <;> rcases hkb with rfl | rfl <;> decide
  rcases quinary_pair_diff_wire dec hsurj ka ha with ⟨ia, ba, hia⟩
  rcases quinary_pair_diff_wire dec hsurj kb hb with ⟨ib, bb, hib⟩
  have hne : ia ≠ ib := fun heq => by
    subst heq; exact quinary_no_shared_wire dec hsurj ka kb hkab ia ba bb hia hib
  let f00 : BitVec 5 → Bool := fun x =>
    (!quinaryOutBit (dec x) ka) && (!quinaryOutBit (dec x) kb)
  have hf_eq : f00 = fun x : BitVec 5 =>
      (x.getLsbD ia.val == !ba) && (x.getLsbD ib.val == !bb) := by
    funext x
    simp only [f00, hia x, hib x]
    cases x.getLsbD ia.val <;> cases ba <;> cases x.getLsbD ib.val <;> cases bb <;> rfl
  have hw8 : weight f00 = 8 := by
    rw [hf_eq]; exact weight_two_wires5_eq_eight ia ib hne (!ba) (!bb)
  let isA1 : Bool := ka == 1
  let isB1 : Bool := kb == 4
  let target : Fin 9 → Int × Int := fun idx =>
    (2 * expZeroVal isA1 ⟨idx.val % 3, by omega⟩, 2 * expZeroVal isB1 ⟨idx.val / 3, by omega⟩)
  have hge9 : 9 ≤ weight f00 := by
    apply le_weight_of_exists f00
      (fun x => (e2m1TwiceVal (dec x).1, e2m1TwiceVal (dec x).2)) target
    · intro a b hab
      simp only [target, Prod.mk.injEq] at hab
      have h0 : a.val % 3 = b.val % 3 := congrArg Fin.val (expZeroVal_twice_inj isA1 hab.1)
      have h1 : a.val / 3 = b.val / 3 := congrArg Fin.val (expZeroVal_twice_inj isB1 hab.2)
      exact Fin.ext (by omega)
    · intro idx
      rcases hsurj _ _ (expZeroVal_isQuinary isA1 _) (expZeroVal_isQuinary isB1 _) with ⟨x, hx0, hx1⟩
      exact ⟨x, Prod.ext hx0 hx1⟩
    · intro x idx hx
      simp only [target, Prod.mk.injEq] at hx
      have hfa : quinaryOutBit (dec x) ka = false := by
        have hbf := expZeroVal_bit_false isA1 (dec x).1 _ hx.1
        rcases hka with rfl | rfl <;> simpa [isA1, quinaryOutBit] using hbf
      have hfb : quinaryOutBit (dec x) kb = false := by
        have hbf := expZeroVal_bit_false isB1 (dec x).2 _ hx.2
        rcases hkb with rfl | rfl <;> simpa [isB1, quinaryOutBit] using hbf
      simp [f00, hfa, hfb]
  omega

theorem quinary_2w5b_to_e2m1_four_lop3_and_wire_bound :
    (∀ w0 w1 : Int, IsQuinary w0 → IsQuinary w1 →
      let (n0, n1) := unpack2q5b (encode2q5b w0 w1)
      e2m1TwiceVal n0 = 2 * w0 ∧ e2m1TwiceVal n1 = 2 * w1) ∧
    (∀ dec : BitVec 5 → BitVec 4 × BitVec 4,
      (∀ w0 w1 : Int, IsQuinary w0 → IsQuinary w1 →
        ∃ x : BitVec 5,
          e2m1TwiceVal (dec x).1 = 2 * w0 ∧ e2m1TwiceVal (dec x).2 = 2 * w1) →
      ∀ k0 k1 k2 k3 : Fin 6,
        k0 ≠ k1 → k0 ≠ k2 → k0 ≠ k3 → k1 ≠ k2 → k1 ≠ k3 → k2 ≠ k3 →
        ¬ (WireOrConst (fun x => quinaryOutBit (dec x) k0) ∧
           WireOrConst (fun x => quinaryOutBit (dec x) k1) ∧
           WireOrConst (fun x => quinaryOutBit (dec x) k2) ∧
           WireOrConst (fun x => quinaryOutBit (dec x) k3))) := by
  refine ⟨?_, ?_⟩
  · intro w0 w1 hw0 hw1
    rcases isQuinary_eq_quinOfFin5 hw0 with ⟨q0, rfl⟩
    rcases isQuinary_eq_quinOfFin5 hw1 with ⟨q1, rfl⟩
    exact unpack2q5b_fin5_exact q0 q1
  · intro dec hsurj k0 k1 k2 k3 h01 h02 h03 h12 h13 h23 ⟨w0, w1, w2, w3⟩
    have h4sub : ∀ a0 a1 a2 a3 : Fin 6,
        a0 ≠ a1 → a0 ≠ a2 → a0 ≠ a3 → a1 ≠ a2 → a1 ≠ a3 → a2 ≠ a3 →
        let S : List (Fin 6) := [a0, a1, a2, a3]
        ((1 : Fin 6) ∈ S ∧ (2 : Fin 6) ∈ S) ∨
        ((4 : Fin 6) ∈ S ∧ (5 : Fin 6) ∈ S) ∨
        (((1 : Fin 6) ∈ S ∨ (2 : Fin 6) ∈ S) ∧ ((4 : Fin 6) ∈ S ∨ (5 : Fin 6) ∈ S)) := by
      decide
    have hmem : ∀ k : Fin 6, k ∈ ([k0, k1, k2, k3] : List (Fin 6)) →
        WireOrConst (fun x => quinaryOutBit (dec x) k) := by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact w0
      · exact w1
      · exact w2
      · exact w3
    rcases h4sub k0 k1 k2 k3 h01 h02 h03 h12 h13 h23 with
      ⟨hm1, hm2⟩ | ⟨hm4, hm5⟩ | ⟨hm12, hm45⟩
    · exact quinary_no_both_exp0 dec hsurj (hmem 1 hm1) (hmem 2 hm2)
    · exact quinary_no_both_exp1 dec hsurj (hmem 4 hm4) (hmem 5 hm5)
    · rcases hm12 with hm1 | hm2 <;> rcases hm45 with hm4 | hm5
      · exact quinary_no_cross_exp dec hsurj 1 4 (Or.inl rfl) (Or.inl rfl) (hmem 1 hm1) (hmem 4 hm4)
      · exact quinary_no_cross_exp dec hsurj 1 5 (Or.inl rfl) (Or.inr rfl) (hmem 1 hm1) (hmem 5 hm5)
      · exact quinary_no_cross_exp dec hsurj 2 4 (Or.inr rfl) (Or.inl rfl) (hmem 2 hm2) (hmem 4 hm4)
      · exact quinary_no_cross_exp dec hsurj 2 5 (Or.inr rfl) (Or.inr rfl) (hmem 2 hm2) (hmem 5 hm5)

end Sparse24E2M1Lop3
