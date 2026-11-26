/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Fp8E4m3Lop3.BitSlicedCircuits

/-!
# Universal `LOP3` DAG Fan-In & Depth Lower Bounds (`LowerBounds.lean`)

Proves `fp8_e4m3_lop3_fanin_lower_bound`:
1. **Universal Gate-Count Fan-In Lower Bound (Arbitrary `LOP3` DAGs):**
   For ANY `n : Nat`, ANY care domain `P : BitVec n → Bool`, and ANY single-output `LOP3` DAG
   `d : SingleOutLop3Dag n` (with arbitrary gate sharing and fan-out):
   `essentialVarCountOn P d.eval ≤ 2 * d.gates.length + 1`
   (so `k` essential variables forces `d.gates.length ≥ k / 2`, i.e. `⌈(k - 1)/2⌉` `LOP3` gates).
2. **Universal Depth Fan-In Lower Bound (Arbitrary `LOP3` DAGs):**
   For ANY `n : Nat`, ANY care domain `P : BitVec n → Bool`, and ANY `d : SingleOutLop3Dag n`:
   `essentialVarCountOn P d.eval ≤ 3 ^ d.depth`.
3. **Exact FP8-E4M3FN Essential-Variable Profiles & Tight Instantiations:**
   - `e4m3_rsqrt_pos` (`isPosFiniteE4M3`): essential variable counts `[7, 7, 7, 7, 6, 7, 7, 0]`,
     forcing `≥ 3` `LOP3` gates and depth `≥ 2` on every active output bit `y0..y6`.
   - `e4m3_rsqrt_full` (all 256 codes): essential variable counts `[8, 8, 8, 8, 7, 8, 8, 0]`,
     forcing `≥ 4` `LOP3` gates on `y0..y3, y5, y6` and `≥ 3` on `y4`.
   - `e4m3_gelu` bit `y6` (`isFiniteE4M3`): `2` essential variables (`≥ 1` `LOP3`, **tight**).
   - `e4m3_silu` bit `y7` (`isFiniteE4M3`): `1` essential variable (`0` `LOP3`, **tight**).
-/

namespace Fp8E4m3Lop3

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-! ## 1. Pure-`Init` List Cardinality & Bit-Mask Helpers -/

private theorem nodup_filter_aux {α : Type} (p : α → Bool) :
    ∀ l : List α, l.Nodup → (l.filter p).Nodup := by
  intro l hnd
  induction l with
  | nil => simp
  | cons a tl ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.filter_cons]
    cases p a
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih hnd.2
    · simp only [↓reduceIte]
      rw [List.nodup_cons]
      refine ⟨?_, ih hnd.2⟩
      intro hmem
      rw [List.mem_filter] at hmem
      exact hnd.1 hmem.1

private theorem nodup_map_inj_aux {α β : Type} (f : α → β)
    (hinj : ∀ x y, f x = f y → x = y) :
    ∀ l : List α, l.Nodup → (l.map f).Nodup := by
  intro l hnd
  induction l with
  | nil => simp
  | cons a tl ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hnd.2⟩
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨b, hb, hfb⟩
    have hEq := hinj b a hfb
    subst hEq
    exact hnd.1 hb

private theorem nodup_subset_length_le {α : Type} [DecidableEq α] :
    ∀ (l s : List α), l.Nodup → (∀ x ∈ l, x ∈ s) → l.length ≤ s.length := by
  intro l
  induction l with
  | nil => intro _ _ _; exact Nat.zero_le _
  | cons a tl ih =>
    intro s hnd hsub
    rw [List.nodup_cons] at hnd
    have ha : a ∈ s := hsub a (by simp)
    have hlt : (s.filter (· != a)).length < s.length := by
      clear ih hnd hsub
      induction s with
      | nil => simp at ha
      | cons y ys ihy =>
        simp only [List.mem_cons] at ha
        by_cases hya : y = a
        · subst hya
          simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.length_cons]
          have := List.length_filter_le (· != y) ys
          omega
        · have hne : (y != a) = true := bne_iff_ne.mpr hya
          have hmem : a ∈ ys := ha.resolve_left (fun h => hya h.symm)
          simp only [List.filter_cons, hne, ↓reduceIte, List.length_cons]
          exact Nat.succ_lt_succ (ihy hmem)
    have htl_sub : ∀ x ∈ tl, x ∈ s.filter (· != a) := by
      intro x hx
      rw [List.mem_filter]
      refine ⟨hsub x (by simp [hx]), bne_iff_ne.mpr ?_⟩
      intro hEq
      subst hEq
      exact hnd.1 hx
    have hle := ih (s.filter (· != a)) hnd.2 htl_sub
    simp only [List.length_cons]
    omega

private theorem anyPow2_eq_true_iff (p : Nat → Bool) :
    ∀ d base, anyPow2 p d base = true ↔ ∃ k, base ≤ k ∧ k < base + 2 ^ d ∧ p k = true := by
  intro d
  induction d with
  | zero =>
    intro base
    simp only [anyPow2, Nat.pow_zero]
    constructor
    · intro h; exact ⟨base, Nat.le_refl _, by omega, h⟩
    · rintro ⟨k, h1, h2, hp⟩
      have hEq : k = base := by omega
      subst hEq; exact hp
  | succ d ih =>
    intro base
    simp only [anyPow2, Bool.or_eq_true, ih]
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by
      rw [Nat.pow_succ, Nat.mul_two]
    constructor
    · rintro (⟨k, h1, h2, hp⟩ | ⟨k, h1, h2, hp⟩)
      · exact ⟨k, h1, by omega, hp⟩
      · exact ⟨k, by omega, by omega, hp⟩
    · rintro ⟨k, h1, h2, hp⟩
      by_cases hlt : k < base + 2 ^ d
      · exact Or.inl ⟨k, h1, hlt, hp⟩
      · exact Or.inr ⟨k, by omega, by omega, hp⟩

private theorem isEssentialVarOn_exists {n : Nat} {P : BitVec n → Bool} {f : BitVec n → Bool}
    {i : Fin n} (h : isEssentialVarOn P f i = true) :
    ∃ x : BitVec n, f x ≠ f (flipBit x i) := by
  unfold isEssentialVarOn at h
  rw [anyPow2_eq_true_iff] at h
  rcases h with ⟨k, _, _, hcond⟩
  simp only [Bool.and_eq_true, bne_iff_ne] at hcond
  exact ⟨BitVec.ofNat n k, hcond.2⟩

private theorem testBit_toNat_ge_false {n : Nat} (x : BitVec n) {k : Nat} (hk : n ≤ k) :
    x.toNat.testBit k = false := by
  have hlt : x.toNat < 2 ^ k := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) hk)
  exact Nat.testBit_lt_two_pow hlt

private theorem flipBit_testBit_ne {n : Nat} (x : BitVec n) (i : Fin n) {w : Nat} (hw : w ≠ i.val) :
    (flipBit x i).toNat.testBit w = x.toNat.testBit w := by
  by_cases hwn : w < n
  · change (flipBit x i).getLsbD w = x.getLsbD w
    simp only [flipBit, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, hwn, decide_true, Bool.true_and]
    by_cases hlt : w < i.val
    · simp [hlt]
    · have hsub : w - i.val ≠ 0 := by omega
      have hlsb : (1#n).getLsbD (w - i.val) = false := by
        rw [BitVec.getLsbD_ofNat]
        cases h : w - i.val with
        | zero => exact absurd h hsub
        | succ k => simp [Nat.testBit_succ]
      simp [hlt, hlsb]
  · rw [testBit_toNat_ge_false (flipBit x i) (by omega), testBit_toNat_ge_false x (by omega)]

private theorem testBit_or_one_shl (m idx w : Nat) :
    (m ||| (1 <<< idx)).testBit w = (m.testBit w || (w == idx)) := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h : w = idx
  · subst h; simp
  · have hne : (w == idx) = false := beq_false_of_ne h
    rw [hne, Bool.or_false]
    by_cases hge : idx ≤ w
    · have hpos : w - idx ≠ 0 := by omega
      simp [hge, Nat.testBit_one_eq_true_iff_self_eq_zero, hpos]
    · simp [hge]

/-! ## 2. Universal Gate-Count Fan-In Bound (`essentialVarCountOn P d.eval ≤ 2 * d.gates.length + 1`) -/

private def expandFrontier : List Lop3Gate → Nat → List Nat → List Nat
  | [], _, F => F
  | g :: gs, base, F =>
      let F' := expandFrontier gs (base + 1) F
      if F'.contains base then
        g.a :: g.b :: g.c :: F'.filter (· != base)
      else
        F'

private theorem filter_ne_length_lt {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (a : α) (h : xs.contains a = true) :
    (xs.filter (· != a)).length < xs.length := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at h
    by_cases hxa : x = a
    · subst hxa
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have hle : (xs.filter (· != x)).length ≤ xs.length := List.length_filter_le _ _
      omega
    · have hne : (x != a) = true := bne_iff_ne.mpr hxa
      have hmem : xs.contains a = true := by
        cases h with
        | inl h1 => exact absurd h1.symm hxa
        | inr h2 => exact h2
      simp only [List.filter_cons, hne, ↓reduceIte, List.length_cons]
      exact Nat.succ_lt_succ (ih hmem)

private theorem expandFrontier_length (gates : List Lop3Gate) (base : Nat) (F : List Nat) :
    (expandFrontier gates base F).length ≤ F.length + 2 * gates.length := by
  induction gates generalizing base with
  | nil => simp [expandFrontier]
  | cons g gs ih =>
    simp only [expandFrontier, List.length_cons]
    have hih := ih (base + 1)
    by_cases hc : (expandFrontier gs (base + 1) F).contains base = true
    · simp only [hc, ↓reduceIte, List.length_cons]
      have hlt := filter_ne_length_lt (expandFrontier gs (base + 1) F) base hc
      omega
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      omega

private theorem expandFrontier_agree (gates : List Lop3Gate) (base : Nat) (F : List Nat)
    (m1 m2 : Nat)
    (hzero1 : ∀ k, base ≤ k → m1.testBit k = false)
    (hzero2 : ∀ k, base ≤ k → m2.testBit k = false)
    (hagree : ∀ w ∈ expandFrontier gates base F, m1.testBit w = m2.testBit w) :
    ∀ w ∈ F, (evalGatesMask gates base m1).testBit w = (evalGatesMask gates base m2).testBit w := by
  induction gates generalizing base m1 m2 with
  | nil =>
    simpa [expandFrontier, evalGatesMask] using hagree
  | cons g gs ih =>
    simp only [expandFrontier] at hagree
    simp only [evalGatesMask]
    have hz1' : ∀ k, base + 1 ≤ k →
        (if lop3 g.imm8 (m1.testBit g.a) (m1.testBit g.b) (m1.testBit g.c) = true
         then m1 ||| (1 <<< base) else m1).testBit k = false := by
      intro k hk
      have hne : (k == base) = false := beq_false_of_ne (by omega)
      cases lop3 g.imm8 (m1.testBit g.a) (m1.testBit g.b) (m1.testBit g.c)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hzero1 k (by omega)
      · simp only [↓reduceIte]
        rw [testBit_or_one_shl, hne, Bool.or_false]
        exact hzero1 k (by omega)
    have hz2' : ∀ k, base + 1 ≤ k →
        (if lop3 g.imm8 (m2.testBit g.a) (m2.testBit g.b) (m2.testBit g.c) = true
         then m2 ||| (1 <<< base) else m2).testBit k = false := by
      intro k hk
      have hne : (k == base) = false := beq_false_of_ne (by omega)
      cases lop3 g.imm8 (m2.testBit g.a) (m2.testBit g.b) (m2.testBit g.c)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hzero2 k (by omega)
      · simp only [↓reduceIte]
        rw [testBit_or_one_shl, hne, Bool.or_false]
        exact hzero2 k (by omega)
    apply ih (base + 1) _ _ hz1' hz2'
    intro w hw
    by_cases hc : (expandFrontier gs (base + 1) F).contains base = true
    · simp only [hc, ↓reduceIte] at hagree
      have ha : m1.testBit g.a = m2.testBit g.a := hagree g.a (by simp)
      have hb : m1.testBit g.b = m2.testBit g.b := hagree g.b (by simp)
      have hc' : m1.testBit g.c = m2.testBit g.c := hagree g.c (by simp)
      have hv : lop3 g.imm8 (m1.testBit g.a) (m1.testBit g.b) (m1.testBit g.c) =
                lop3 g.imm8 (m2.testBit g.a) (m2.testBit g.b) (m2.testBit g.c) := by
        rw [ha, hb, hc']
      by_cases hwb : w = base
      · subst hwb
        rw [hv]
        cases lop3 g.imm8 (m2.testBit g.a) (m2.testBit g.b) (m2.testBit g.c)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hzero1 w (Nat.le_refl _), hzero2 w (Nat.le_refl _)]
        · simp only [↓reduceIte]
          rw [testBit_or_one_shl, testBit_or_one_shl, beq_self_eq_true, Bool.or_true, Bool.or_true]
      · have hwf : w ∈ (expandFrontier gs (base + 1) F).filter (· != base) := by
          simp [List.mem_filter, hw, bne_iff_ne, hwb]
        have hmw : m1.testBit w = m2.testBit w := hagree w (by simp [hwf])
        rw [hv]
        cases lop3 g.imm8 (m2.testBit g.a) (m2.testBit g.b) (m2.testBit g.c)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact hmw
        · simp only [↓reduceIte]
          rw [testBit_or_one_shl, testBit_or_one_shl, hmw]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hagree
      have hwb : w ≠ base := by
        intro hEq
        have hmem : (expandFrontier gs (base + 1) F).contains base = true := by
          rw [List.contains_iff_mem]
          exact hEq ▸ hw
        exact hc hmem
      have hmw : m1.testBit w = m2.testBit w := hagree w hw
      have hne : (w == base) = false := beq_false_of_ne hwb
      cases lop3 g.imm8 (m1.testBit g.a) (m1.testBit g.b) (m1.testBit g.c) <;>
      cases lop3 g.imm8 (m2.testBit g.a) (m2.testBit g.b) (m2.testBit g.c) <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
      · exact hmw
      · rw [testBit_or_one_shl, hne, Bool.or_false]; exact hmw
      · rw [testBit_or_one_shl, hne, Bool.or_false]; exact hmw
      · rw [testBit_or_one_shl, testBit_or_one_shl, hne, Bool.or_false, Bool.or_false]; exact hmw

private theorem essential_le_support_length {n : Nat} {P : BitVec n → Bool} {f : BitVec n → Bool}
    (S : List Nat)
    (hdep : ∀ x y : BitVec n, (∀ w ∈ S, x.toNat.testBit w = y.toNat.testBit w) → f x = f y) :
    essentialVarCountOn P f ≤ S.length := by
  unfold essentialVarCountOn
  let L := (List.finRange n).filter (isEssentialVarOn P f)
  have hnd : (L.map Fin.val).Nodup := by
    have hnd0 : (List.finRange n).Nodup := List.nodup_finRange n
    have hnd1 : L.Nodup := nodup_filter_aux _ _ hnd0
    exact nodup_map_inj_aux Fin.val (fun _ _ h => Fin.ext h) L hnd1
  have hsub : ∀ v ∈ L.map Fin.val, v ∈ S := by
    intro v hv
    rw [List.mem_map] at hv
    rcases hv with ⟨i, hi, rfl⟩
    rw [List.mem_filter] at hi
    rcases isEssentialVarOn_exists hi.2 with ⟨x, hne⟩
    by_cases hmem : i.val ∈ S
    · exact hmem
    · exfalso
      apply hne
      apply hdep x (flipBit x i)
      intro w hw
      have hwi : w ≠ i.val := fun hEq => hmem (hEq ▸ hw)
      exact (flipBit_testBit_ne x i hwi).symm
  have hle := nodup_subset_length_le (L.map Fin.val) S hnd hsub
  simpa [List.length_map] using hle

/-- Universal gate-count fan-in lower bound for ANY single-output `LOP3` DAG. -/
theorem lop3_dag_essential_le_two_gates_plus_one {n : Nat} (P : BitVec n → Bool)
    (d : SingleOutLop3Dag n) :
    essentialVarCountOn P d.eval ≤ 2 * d.gates.length + 1 := by
  cases hout : d.out with
  | const b =>
    have hconst : essentialVarCountOn P d.eval ≤ ([] : List Nat).length := by
      apply essential_le_support_length []
      intro x y _
      simp [SingleOutLop3Dag.eval, hout, evalOutMask]
    simp only [List.length_nil] at hconst
    omega
  | node idx =>
    let S := expandFrontier d.gates n [idx]
    have hlen : S.length ≤ 2 * d.gates.length + 1 := by
      have h := expandFrontier_length d.gates n [idx]
      simp only [List.length_singleton] at h
      dsimp only [S]
      omega
    have hdep : essentialVarCountOn P d.eval ≤ S.length := by
      apply essential_le_support_length S
      intro x y hagree
      simp only [SingleOutLop3Dag.eval, hout, evalOutMask]
      exact expandFrontier_agree d.gates n [idx] x.toNat y.toNat
        (fun _ hk => testBit_toNat_ge_false x hk)
        (fun _ hk => testBit_toNat_ge_false y hk)
        hagree idx (by simp)
    exact Nat.le_trans hdep hlen

/-! ## 3. Universal Depth Fan-In Bound (`essentialVarCountOn P d.eval ≤ 3 ^ d.depth`) -/

private theorem foldl_support_depth_inv {n : Nat} (gates : List Lop3Gate)
    (sup0 : Array (List Nat)) (ds0 : Array Nat) (m1 m2 : Nat)
    (hsize : sup0.size = ds0.size)
    (hbase : n ≤ ds0.size)
    (hbound : ∀ w, w < ds0.size → ∀ i ∈ sup0.getD w [], i < n)
    (hzero1 : ∀ k, ds0.size ≤ k → m1.testBit k = false)
    (hzero2 : ∀ k, ds0.size ≤ k → m2.testBit k = false)
    (hlen : ∀ w, w < ds0.size → (sup0.getD w []).length ≤ 3 ^ (ds0.getD w 0))
    (hinv : ∀ w, w < ds0.size →
      (∀ i ∈ sup0.getD w [], m1.testBit i = m2.testBit i) →
      m1.testBit w = m2.testBit w) :
    let supF := gates.foldl (fun acc g =>
      acc.push (acc.getD g.a [] ++ acc.getD g.b [] ++ acc.getD g.c [])) sup0
    let dsF := gates.foldl (fun acc g =>
      acc.push (1 + max (acc.getD g.a 0) (max (acc.getD g.b 0) (acc.getD g.c 0)))) ds0
    let m1F := evalGatesMask gates ds0.size m1
    let m2F := evalGatesMask gates ds0.size m2
    supF.size = dsF.size ∧
    dsF.size = ds0.size + gates.length ∧
    (∀ w, w < dsF.size → ∀ i ∈ supF.getD w [], i < n) ∧
    (∀ k, dsF.size ≤ k → m1F.testBit k = false ∧ m2F.testBit k = false) ∧
    (∀ w, w < dsF.size → (supF.getD w []).length ≤ 3 ^ (dsF.getD w 0)) ∧
    (∀ w, w < dsF.size →
      (∀ i ∈ supF.getD w [], m1.testBit i = m2.testBit i) →
      m1F.testBit w = m2F.testBit w) := by
  induction gates generalizing sup0 ds0 m1 m2 with
  | nil =>
    exact ⟨hsize, by simp, hbound, fun k hk => ⟨hzero1 k hk, hzero2 k hk⟩, hlen, hinv⟩
  | cons g gs ih =>
    simp only [List.foldl_cons, evalGatesMask]
    let newSup := sup0.getD g.a [] ++ sup0.getD g.b [] ++ sup0.getD g.c []
    let newD := 1 + max (ds0.getD g.a 0) (max (ds0.getD g.b 0) (ds0.getD g.c 0))
    let sup1 := sup0.push newSup
    let ds1 := ds0.push newD
    let v1 := lop3 g.imm8 (m1.testBit g.a) (m1.testBit g.b) (m1.testBit g.c)
    let v2 := lop3 g.imm8 (m2.testBit g.a) (m2.testBit g.b) (m2.testBit g.c)
    let m1' := if v1 then m1 ||| (1 <<< ds0.size) else m1
    let m2' := if v2 then m2 ||| (1 <<< ds0.size) else m2
    have hsz1 : sup1.size = ds1.size := by simp [sup1, ds1, hsize]
    have hds1 : ds1.size = ds0.size + 1 := by simp [ds1]
    have hgetD_sup : ∀ w, sup1.getD w [] = if w = ds0.size then newSup else sup0.getD w [] := by
      intro w
      simp only [sup1, Array.getD, Array.size_push, hsize]
      by_cases hlt : w < ds0.size
      · have hlt1 : w < ds0.size + 1 := by omega
        have hne : w ≠ ds0.size := by omega
        have hlt_s : w < sup0.size := by omega
        simp [hlt, hlt1, hne, Array.getElem_push_lt hlt_s]
      · by_cases hEq : w = ds0.size
        · subst hEq
          have hlt1 : ds0.size < ds0.size + 1 := by omega
          simp only [hlt1, ↓reduceDIte, ↓reduceIte]
          have hpush : (sup0.push newSup)[sup0.size]'(by simp) = newSup := Array.getElem_push_eq
          simpa [hsize] using hpush
        · have hge : ¬(w < ds0.size + 1) := by omega
          simp [hlt, hge, hEq]
    have hgetD_ds : ∀ w, ds1.getD w 0 = if w = ds0.size then newD else ds0.getD w 0 := by
      intro w
      simp only [ds1, Array.getD, Array.size_push]
      by_cases hlt : w < ds0.size
      · have hlt1 : w < ds0.size + 1 := by omega
        have hne : w ≠ ds0.size := by omega
        simp [hlt, hlt1, hne, Array.getElem_push_lt hlt]
      · by_cases hEq : w = ds0.size
        · subst hEq
          simp [Array.getElem_push_eq]
        · have hge : ¬(w < ds0.size + 1) := by omega
          simp [hlt, hge, hEq]
    have hbound_all : ∀ u, ∀ i ∈ sup0.getD u [], i < n := by
      intro u i hi
      by_cases hu : u < ds0.size
      · exact hbound u hu i hi
      · simp [Array.getD, hsize, hu] at hi
    have hbound1 : ∀ w, w < ds1.size → ∀ i ∈ sup1.getD w [], i < n := by
      intro w hw i hi
      rw [hgetD_sup] at hi
      by_cases hEq : w = ds0.size
      · simp only [hEq, ↓reduceIte, newSup, List.mem_append] at hi
        rcases hi with (hi | hi) | hi
        · exact hbound_all g.a i hi
        · exact hbound_all g.b i hi
        · exact hbound_all g.c i hi
      · simp only [hEq, ↓reduceIte] at hi
        exact hbound w (by omega) i hi
    have hgetD_len_all : ∀ u, (sup0.getD u []).length ≤ 3 ^ (ds0.getD u 0) := by
      intro u
      by_cases hu : u < ds0.size
      · exact hlen u hu
      · simp only [Array.getD, hsize, hu, ↓reduceDIte, List.length_nil]
        exact Nat.zero_le _
    have hlen1 : ∀ w, w < ds1.size → (sup1.getD w []).length ≤ 3 ^ (ds1.getD w 0) := by
      intro w hw
      rw [hgetD_sup, hgetD_ds]
      by_cases hEq : w = ds0.size
      · simp only [hEq, ↓reduceIte, newSup, newD, List.length_append]
        have ha := hgetD_len_all g.a
        have hb := hgetD_len_all g.b
        have hc := hgetD_len_all g.c
        let M := max (ds0.getD g.a 0) (max (ds0.getD g.b 0) (ds0.getD g.c 0))
        have hpa : 3 ^ ds0.getD g.a 0 ≤ 3 ^ M := Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
        have hpb : 3 ^ ds0.getD g.b 0 ≤ 3 ^ M :=
          Nat.pow_le_pow_right (by omega) (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
        have hpc : 3 ^ ds0.getD g.c 0 ≤ 3 ^ M :=
          Nat.pow_le_pow_right (by omega) (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
        have hpow : 3 ^ (1 + M) = 3 ^ M + 3 ^ M + 3 ^ M := by
          rw [Nat.add_comm 1 M, Nat.pow_succ]
          omega
        change _ ≤ 3 ^ (1 + M)
        omega
      · simp only [hEq, ↓reduceIte]
        exact hlen w (by omega)
    have hzero1' : ∀ k, ds1.size ≤ k → m1'.testBit k = false := by
      intro k hk
      have hne : (k == ds0.size) = false := beq_false_of_ne (by omega)
      dsimp only [m1']
      cases v1
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hzero1 k (by omega)
      · simp only [↓reduceIte]
        rw [testBit_or_one_shl, hne, Bool.or_false]
        exact hzero1 k (by omega)
    have hzero2' : ∀ k, ds1.size ≤ k → m2'.testBit k = false := by
      intro k hk
      have hne : (k == ds0.size) = false := beq_false_of_ne (by omega)
      dsimp only [m2']
      cases v2
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hzero2 k (by omega)
      · simp only [↓reduceIte]
        rw [testBit_or_one_shl, hne, Bool.or_false]
        exact hzero2 k (by omega)
    have hm1'_lt : ∀ u, u < ds0.size → m1'.testBit u = m1.testBit u := by
      intro u hu
      have hne : (u == ds0.size) = false := beq_false_of_ne (by omega)
      dsimp only [m1']
      cases v1
      · simp only [Bool.false_eq_true, ↓reduceIte]
      · simp only [↓reduceIte]
        rw [testBit_or_one_shl, hne, Bool.or_false]
    have hm2'_lt : ∀ u, u < ds0.size → m2'.testBit u = m2.testBit u := by
      intro u hu
      have hne : (u == ds0.size) = false := beq_false_of_ne (by omega)
      dsimp only [m2']
      cases v2
      · simp only [Bool.false_eq_true, ↓reduceIte]
      · simp only [↓reduceIte]
        rw [testBit_or_one_shl, hne, Bool.or_false]
    have hinv_all : ∀ u, (∀ i ∈ sup0.getD u [], m1.testBit i = m2.testBit i) →
        m1.testBit u = m2.testBit u := by
      intro u h
      by_cases hu : u < ds0.size
      · exact hinv u hu h
      · rw [hzero1 u (by omega), hzero2 u (by omega)]
    have hinv1 : ∀ w, w < ds1.size →
        (∀ i ∈ sup1.getD w [], m1'.testBit i = m2'.testBit i) →
        m1'.testBit w = m2'.testBit w := by
      intro w hw hag
      have hag0 : ∀ i ∈ sup1.getD w [], m1.testBit i = m2.testBit i := by
        intro i hi
        have hin : i < ds0.size := Nat.lt_of_lt_of_le (hbound1 w hw i hi) hbase
        rw [← hm1'_lt i hin, ← hm2'_lt i hin]
        exact hag i hi
      rw [hgetD_sup] at hag0
      by_cases hEq : w = ds0.size
      · subst hEq
        simp only [↓reduceIte, newSup, List.mem_append] at hag0
        have ha : m1.testBit g.a = m2.testBit g.a :=
          hinv_all g.a (fun i hi => hag0 i (Or.inl (Or.inl hi)))
        have hb : m1.testBit g.b = m2.testBit g.b :=
          hinv_all g.b (fun i hi => hag0 i (Or.inl (Or.inr hi)))
        have hc : m1.testBit g.c = m2.testBit g.c :=
          hinv_all g.c (fun i hi => hag0 i (Or.inr hi))
        have hv : v1 = v2 := by
          dsimp only [v1, v2]
          rw [ha, hb, hc]
        dsimp only [m1', m2']
        rw [hv]
        cases v2
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hzero1 ds0.size (Nat.le_refl _), hzero2 ds0.size (Nat.le_refl _)]
        · simp only [↓reduceIte]
          rw [testBit_or_one_shl, testBit_or_one_shl, beq_self_eq_true, Bool.or_true, Bool.or_true]
      · simp only [hEq, ↓reduceIte] at hag0
        have hw0 : w < ds0.size := by omega
        rw [hm1'_lt w hw0, hm2'_lt w hw0]
        exact hinv w hw0 hag0
    have hrec := ih sup1 ds1 m1' m2' hsz1 (by omega) hbound1 hzero1' hzero2' hlen1 hinv1
    rcases hrec with ⟨hszF, hdsF, hboundF, hzeroF, hlenF, hinvF⟩
    refine ⟨hszF, ?_, hboundF, ?_, hlenF, ?_⟩
    · rw [hdsF, hds1, List.length_cons]
      omega
    · intro k hk
      rw [← hds1]
      exact hzeroF k hk
    · intro w hw hag
      have hag' : ∀ i ∈ (gs.foldl (fun acc g =>
          acc.push (acc.getD g.a [] ++ acc.getD g.b [] ++ acc.getD g.c [])) sup1).getD w [],
          m1'.testBit i = m2'.testBit i := by
        intro i hi
        have hin : i < ds0.size := Nat.lt_of_lt_of_le (hboundF w hw i hi) hbase
        rw [hm1'_lt i hin, hm2'_lt i hin]
        exact hag i hi
      rw [← hds1]
      exact hinvF w hw hag'

/-- Universal depth fan-in lower bound for ANY single-output `LOP3` DAG. -/
theorem lop3_dag_essential_le_three_pow_depth {n : Nat} (P : BitVec n → Bool)
    (d : SingleOutLop3Dag n) :
    essentialVarCountOn P d.eval ≤ 3 ^ d.depth := by
  cases hout : d.out with
  | const b =>
    have hconst : essentialVarCountOn P d.eval ≤ ([] : List Nat).length := by
      apply essential_le_support_length []
      intro x y _
      simp [SingleOutLop3Dag.eval, hout, evalOutMask]
    simp only [List.length_nil] at hconst
    exact Nat.le_trans hconst (Nat.zero_le _)
  | node idx =>
    let sup0 : Array (List Nat) := Array.ofFn (fun i : Fin n => [i.val])
    let ds0 : Array Nat := Array.replicate n 0
    have hsz0 : sup0.size = ds0.size := by simp [sup0, ds0]
    have hds0 : ds0.size = n := by simp [ds0]
    have hgetD_sup0 : ∀ w, w < n → sup0.getD w [] = [w] := by
      intro w hw
      simp [sup0, Array.getD, hw]
    have hgetD_ds0 : ∀ w, w < n → ds0.getD w 0 = 0 := by
      intro w hw
      simp [ds0, Array.getD, hw]
    let supF := d.gates.foldl (fun acc g =>
      acc.push (acc.getD g.a [] ++ acc.getD g.b [] ++ acc.getD g.c [])) sup0
    let dsF := d.gates.foldl (fun acc g =>
      acc.push (1 + max (acc.getD g.a 0) (max (acc.getD g.b 0) (acc.getD g.c 0)))) ds0
    have hrun : ∀ x y : BitVec n,
        supF.size = dsF.size ∧
        dsF.size = n + d.gates.length ∧
        (∀ w, w < dsF.size → ∀ i ∈ supF.getD w [], i < n) ∧
        (∀ k, dsF.size ≤ k →
          (evalGatesMask d.gates n x.toNat).testBit k = false ∧
          (evalGatesMask d.gates n y.toNat).testBit k = false) ∧
        (∀ w, w < dsF.size → (supF.getD w []).length ≤ 3 ^ (dsF.getD w 0)) ∧
        (∀ w, w < dsF.size →
          (∀ i ∈ supF.getD w [], x.toNat.testBit i = y.toNat.testBit i) →
          (evalGatesMask d.gates n x.toNat).testBit w =
          (evalGatesMask d.gates n y.toNat).testBit w) := by
      intro x y
      have h := foldl_support_depth_inv (n := n) d.gates sup0 ds0 x.toNat y.toNat
        hsz0 (by omega)
        (fun w hw i hi => by
          rw [hds0] at hw
          rw [hgetD_sup0 w hw] at hi
          simp only [List.mem_singleton] at hi
          omega)
        (fun k hk => testBit_toNat_ge_false x (by omega))
        (fun k hk => testBit_toNat_ge_false y (by omega))
        (fun w hw => by
          rw [hds0] at hw
          rw [hgetD_sup0 w hw, hgetD_ds0 w hw]
          simp)
        (fun w hw hag => by
          rw [hds0] at hw
          rw [hgetD_sup0 w hw] at hag
          exact hag w (by simp))
      simpa [hds0, supF, dsF] using h
    by_cases hidx : idx < dsF.size
    · have h0 := hrun (0#n) (0#n)
      have hlen : (supF.getD idx []).length ≤ 3 ^ (dsF.getD idx 0) := h0.2.2.2.2.1 idx hidx
      have hdep : essentialVarCountOn P d.eval ≤ (supF.getD idx []).length := by
        apply essential_le_support_length (supF.getD idx [])
        intro x y hag
        simp only [SingleOutLop3Dag.eval, hout, evalOutMask]
        exact (hrun x y).2.2.2.2.2 idx hidx hag
      have hdEq : d.depth = dsF.getD idx 0 := by
        simp [SingleOutLop3Dag.depth, hout, dsF, ds0]
      rw [hdEq]
      exact Nat.le_trans hdep hlen
    · have hzero : essentialVarCountOn P d.eval ≤ ([] : List Nat).length := by
        apply essential_le_support_length []
        intro x y _
        simp only [SingleOutLop3Dag.eval, hout, evalOutMask]
        have hz := (hrun x y).2.2.2.1 idx (by omega)
        rw [hz.1, hz.2]
      simp only [List.length_nil] at hzero
      exact Nat.le_trans hzero (Nat.zero_le _)

/-! ## 4. Exact FP8-E4M3FN Essential-Variable Profiles & Headline Theorem 5 -/

private theorem anyPow2_congr {p q : Nat → Bool} (h : ∀ k, p k = q k) :
    ∀ d base, anyPow2 p d base = anyPow2 q d base := by
  intro d
  induction d with
  | zero => intro base; exact h base
  | succ d ih =>
    intro base
    simp only [anyPow2, ih base, ih (base + 2 ^ d)]

private theorem essentialVarCountOn_congr {n : Nat} {P : BitVec n → Bool}
    {f g : BitVec n → Bool} (h : ∀ x : BitVec n, P x = true → f x = g x) :
    essentialVarCountOn P f = essentialVarCountOn P g := by
  have hi : ∀ i : Fin n, isEssentialVarOn P f i = isEssentialVarOn P g i := by
    intro i
    unfold isEssentialVarOn
    apply anyPow2_congr
    intro k
    dsimp only
    cases hpx : P (BitVec.ofNat n k)
    · simp
    · cases hpx' : P (flipBit (BitVec.ofNat n k) i)
      · simp
      · rw [h _ hpx, h _ hpx']
  have hfun : isEssentialVarOn P f = isEssentialVarOn P g := funext hi
  simp [essentialVarCountOn, hfun]

private theorem rsqrt_pos_ess_profile :
    (List.finRange 8).map (fun k =>
      essentialVarCountOn isPosFiniteE4M3 (outBit8 (evalLop3Dag8 e4m3RsqrtPosDag) k)) =
    [7, 7, 7, 7, 6, 7, 7, 0] := by
  decide

private theorem rsqrt_full_ess_profile :
    (List.finRange 8).map (fun k =>
      essentialVarCount (outBit8 (evalLop3Dag8 e4m3RsqrtFullDag) k)) =
    [8, 8, 8, 8, 7, 8, 8, 0] := by
  have hspec := fp8_e4m3_rsqrt_full_33_lop3_exact
  have heq : ∀ k : Fin 8,
      essentialVarCount (outBit8 (evalLop3Dag8 e4m3RsqrtFullDag) k) =
      essentialVarCount (outBit8 (fun x =>
        if isPosFiniteE4M3 x then evalLop3Dag8 e4m3RsqrtPosDag x else 0x7F#8) k) := by
    intro k
    apply essentialVarCountOn_congr
    intro x _
    unfold outBit8
    cases hpos : isPosFiniteE4M3 x
    · simp [hpos, hspec.2.2.2 x hpos]
    · simp [hpos, (hspec.2.2.1 x hpos).1]
  have hfast :
      (List.finRange 8).map (fun k =>
        essentialVarCount (outBit8 (fun x =>
          if isPosFiniteE4M3 x then evalLop3Dag8 e4m3RsqrtPosDag x else 0x7F#8) k)) =
      [8, 8, 8, 8, 7, 8, 8, 0] := by
    decide
  simpa [heq] using hfast

private theorem gelu_y6_ess_count :
    essentialVarCountOn isFiniteE4M3 (outBit8 (evalLop3Dag8 e4m3GeluDag) 6) = 2 := by
  have hact := fp8_e4m3_activations_lop3_exact
  change essentialVarCountOn isFiniteE4M3 (fun x => (evalLop3Dag8 e4m3GeluDag x).getLsbD 6) = 2
  rw [essentialVarCountOn_congr (g := fun x => lop3 0x04#8 (x.getLsbD 7) (x.getLsbD 6) (x.getLsbD 7))
    (fun x hx => hact.2.2.2.2.2.2.1 x hx)]
  decide

private theorem silu_y7_ess_count :
    essentialVarCountOn isFiniteE4M3 (outBit8 (evalLop3Dag8 e4m3SiluDag) 7) = 1 := by
  have hact := fp8_e4m3_activations_lop3_exact
  change essentialVarCountOn isFiniteE4M3 (fun x => (evalLop3Dag8 e4m3SiluDag x).getLsbD 7) = 1
  rw [essentialVarCountOn_congr (g := fun x => x.getLsbD 7)
    (fun x hx => hact.2.2.2.2.2.2.2.2.2.2 x hx)]
  decide

/-- Theorem 5: Universal `LOP3` DAG fan-in & depth lower bounds instantiated on OCP `FP8-E4M3FN`. -/
theorem fp8_e4m3_lop3_fanin_lower_bound :
    (∀ (n : Nat) (P : BitVec n → Bool) (d : SingleOutLop3Dag n),
      essentialVarCountOn P d.eval ≤ 2 * d.gates.length + 1 ∧
      essentialVarCountOn P d.eval ≤ 3 ^ d.depth) ∧
    (List.finRange 8).map (fun k =>
      essentialVarCountOn isPosFiniteE4M3 (outBit8 (evalLop3Dag8 e4m3RsqrtPosDag) k)) =
      [7, 7, 7, 7, 6, 7, 7, 0] ∧
    (List.finRange 8).map (fun k =>
      essentialVarCount (outBit8 (evalLop3Dag8 e4m3RsqrtFullDag) k)) =
      [8, 8, 8, 8, 7, 8, 8, 0] ∧
    essentialVarCountOn isFiniteE4M3 (outBit8 (evalLop3Dag8 e4m3GeluDag) 6) = 2 ∧
    essentialVarCountOn isFiniteE4M3 (outBit8 (evalLop3Dag8 e4m3SiluDag) 7) = 1 := by
  refine ⟨fun _ P d => ⟨lop3_dag_essential_le_two_gates_plus_one P d,
    lop3_dag_essential_le_three_pow_depth P d⟩,
    rsqrt_pos_ess_profile, rsqrt_full_ess_profile, gelu_y6_ess_count, silu_y7_ess_count⟩

end Fp8E4m3Lop3
