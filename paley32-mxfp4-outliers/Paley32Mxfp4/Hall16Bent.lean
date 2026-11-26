/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Paley32Mxfp4.Defs
import Paley32Mxfp4.Paley32

/-!
# Hall-16 Five Equivalence Classes (`k = 4` vs `k = 8` Duality) & Bent Diagonal Anti-Resonance

Pure Lean 4 `Init` (zero Mathlib, zero `native_decide`) proofs of:
- Theorem 4 (`hall16_five_classes_orthogonality_and_k4_k8_duality`)
- Theorem 5 (`bent_diagonal_n16_anti_resonance_exact`)
-/

namespace Paley32Mxfp4

/-! ### 1. Theorem 5: 4-Variable Bent Diagonal Anti-Resonance on Sylvester-16 -/

theorem bent_diag_orthogonal : isOrthogonal (diagTwist sylvester16 bentDiag16) 16 := by
  funext i j
  revert i j
  decide

set_option maxRecDepth 50000 in
theorem affinePlanes16_length : affinePlanes16.length = 140 := by
  decide

set_option maxRecDepth 50000 in
theorem sylvester16_flat_planes_zero : countFlatAffinePlanes16 sylvester16 = 0 := by
  decide

set_option maxRecDepth 50000 in
theorem bent_diag_flat_planes_80 :
    countFlatAffinePlanes16 (diagTwist sylvester16 bentDiag16) = 80 := by
  decide

theorem bent_diagonal_n16_anti_resonance_exact :
    isOrthogonal (diagTwist sylvester16 bentDiag16) 16 ∧
    affinePlanes16.length = 140 ∧
    countFlatAffinePlanes16 sylvester16 = 0 ∧
    countFlatAffinePlanes16 (diagTwist sylvester16 bentDiag16) = 80 :=
  ⟨bent_diag_orthogonal, affinePlanes16_length,
   sylvester16_flat_planes_zero, bent_diag_flat_planes_80⟩

/-! ### 2. Structural `foldFin` Helpers -/

theorem foldFin_congr {α : Type} {n : Nat} (f g : Fin n → α → α) (acc : α)
    (h : ∀ i a, f i a = g i a) :
    foldFin n f acc = foldFin n g acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ k ih =>
    simp only [foldFin]
    rw [h (Fin.last k) acc]
    exact ih _ _ _ (fun i a => h i.castSucc a)

theorem foldFin_invariant {α : Type} {n : Nat} (P : α → Prop) (f : Fin n → α → α) (acc : α)
    (hacc : P acc) (hstep : ∀ i a, P a → P (f i a)) :
    P (foldFin n f acc) := by
  induction n generalizing acc with
  | zero => exact hacc
  | succ k ih =>
    simp only [foldFin]
    exact ih (fun i a => f i.castSucc a) (f (Fin.last k) acc)
      (hstep (Fin.last k) acc hacc) (fun i a ha => hstep i.castSucc a ha)

/-! ### 3. Theorem 4: Hall-16 Orthogonality & Exhaustive `k = 4` / `k = 8` Counts -/

theorem hall16_I_orthogonal   : isOrthogonal hall16_I   16 := by funext i j; revert i j; decide
theorem hall16_II_orthogonal  : isOrthogonal hall16_II  16 := by funext i j; revert i j; decide
theorem hall16_III_orthogonal : isOrthogonal hall16_III 16 := by funext i j; revert i j; decide
theorem hall16_IV_orthogonal  : isOrthogonal hall16_IV  16 := by funext i j; revert i j; decide
theorem hall16_V_orthogonal   : isOrthogonal hall16_V   16 := by funext i j; revert i j; decide

set_option maxRecDepth 50000 in
theorem hall16_I_k8_count   : countDoublePeak8Subsets16 hall16_I   = 30  := by decide
set_option maxRecDepth 50000 in
theorem hall16_II_k8_count  : countDoublePeak8Subsets16 hall16_II  = 54  := by decide
set_option maxRecDepth 50000 in
theorem hall16_III_k8_count : countDoublePeak8Subsets16 hall16_III = 90  := by decide
set_option maxRecDepth 50000 in
theorem hall16_V_k8_count   : countDoublePeak8Subsets16 hall16_V   = 114 := by decide
set_option maxRecDepth 50000 in
theorem hall16_IV_k8_count  : countDoublePeak8Subsets16 hall16_IV  = 156 := by decide

/-- Fast 16-bit popcount for bitmask-accelerated `countClosedQuads16`. -/
def popcount16 (x : Nat) : Nat :=
  (x &&& 1) + ((x >>> 1) &&& 1) + ((x >>> 2) &&& 1) + ((x >>> 3) &&& 1) +
  ((x >>> 4) &&& 1) + ((x >>> 5) &&& 1) + ((x >>> 6) &&& 1) + ((x >>> 7) &&& 1) +
  ((x >>> 8) &&& 1) + ((x >>> 9) &&& 1) + ((x >>> 10) &&& 1) + ((x >>> 11) &&& 1) +
  ((x >>> 12) &&& 1) + ((x >>> 13) &&& 1) + ((x >>> 14) &&& 1) + ((x >>> 15) &&& 1)

def maxC4FromMasks16 (masks : Array Nat) (c0 c1 c2 c3 : Fin 16) : Nat :=
  let m0 := masks.getD c0.val 0
  let m1 := masks.getD c1.val 0
  let m2 := masks.getD c2.val 0
  let m3 := masks.getD c3.val 0
  let d1 := m0 ^^^ m1
  let d2 := m0 ^^^ m2
  let d3 := m0 ^^^ m3
  let nd1 := 65535 ^^^ d1
  let nd2 := 65535 ^^^ d2
  let nd3 := 65535 ^^^ d3
  let b0 := popcount16 (nd1 &&& nd2 &&& nd3)
  let b1 := popcount16 (d1  &&& nd2 &&& nd3)
  let b2 := popcount16 (nd1 &&& d2  &&& nd3)
  let b3 := popcount16 (d1  &&& d2  &&& nd3)
  let b4 := popcount16 (nd1 &&& nd2 &&& d3)
  let b5 := popcount16 (d1  &&& nd2 &&& d3)
  let b6 := popcount16 (nd1 &&& d2  &&& d3)
  let b7 := popcount16 (d1  &&& d2  &&& d3)
  max (max (max b0 b1) (max b2 b3)) (max (max b4 b5) (max b6 b7))

def countClosedQuads16Fast (masks : Array Nat) : Nat :=
  foldFin 16 (fun c0 acc0 =>
    foldFin 16 (fun c1 acc1 =>
      if c0.val < c1.val then
        foldFin 16 (fun c2 acc2 =>
          if c1.val < c2.val then
            foldFin 16 (fun c3 acc3 =>
              if c2.val < c3.val then
                acc3 + (if maxC4FromMasks16 masks c0 c1 c2 c3 = 4 then 1 else 0)
              else acc3) acc2
          else acc2) acc1
      else acc1) acc0) 0

theorem popcount16_eq_sumFinNat (x : Nat) :
    popcount16 x = sumFinNat 16 (fun r => (x >>> r.val) &&& 1) := by
  simp only [popcount16, sumFinNat, Fin.last, Fin.castSucc, Nat.zero_add]
  rfl

theorem maxC4FromMasks16_eq (masks : Array Nat) (c0 c1 c2 c3 : Fin 16) :
    maxC4FromMasks16 masks c0 c1 c2 c3 = maxC4 (matFromColMasks16 masks) c0 c1 c2 c3 := by
  let m0 := masks.getD c0.val 0
  let m1 := masks.getD c1.val 0
  let m2 := masks.getD c2.val 0
  let m3 := masks.getD c3.val 0
  have hbit3 : ∀ (a b c : Nat) (r : Fin 16),
      ((a &&& b &&& c) >>> r.val) &&& 1 =
      (((a >>> r.val) &&& 1) &&& ((b >>> r.val) &&& 1) &&& ((c >>> r.val) &&& 1)) := by
    intro a b c r
    rw [Nat.shiftRight_and_distrib, Nat.shiftRight_and_distrib, nat_and1_and, nat_and1_and]
  have hxor_bit : ∀ (a b : Nat) (r : Fin 16),
      ((a ^^^ b) >>> r.val) &&& 1 = (((a >>> r.val) &&& 1) ^^^ ((b >>> r.val) &&& 1)) := by
    intro a b r
    rw [Nat.shiftRight_xor_distrib, nat_and1_xor]
  have hones16 : ∀ (r : Fin 16), (65535 >>> r.val) &&& 1 = 1 := by decide
  have hnot_bit : ∀ (a : Nat) (r : Fin 16),
      ((65535 ^^^ a) >>> r.val) &&& 1 = 1 - ((a >>> r.val) &&& 1) := by
    intro a r
    rw [hxor_bit, hones16 r]
    rcases nat_and1_cases (a >>> r.val) with h | h <;> simp [h]
  have hbucket : ∀ (f1 f2 f3 : Bool) (s1 s2 s3 : Int),
      (s1 = if f1 then -1 else 1) → (s2 = if f2 then -1 else 1) → (s3 = if f3 then -1 else 1) →
      popcount16 ((if f1 then m0 ^^^ m1 else 65535 ^^^ (m0 ^^^ m1)) &&&
                  (if f2 then m0 ^^^ m2 else 65535 ^^^ (m0 ^^^ m2)) &&&
                  (if f3 then m0 ^^^ m3 else 65535 ^^^ (m0 ^^^ m3))) =
      c4ForSigns (matFromColMasks16 masks) c0 c1 c2 c3 s1 s2 s3 := by
    intro f1 f2 f3 s1 s2 s3 hs1 hs2 hs3
    rw [popcount16_eq_sumFinNat]
    unfold c4ForSigns matFromColMasks16
    apply sumFinNat_congr
    intro r
    rw [hbit3]
    have hsel : ∀ (f : Bool) (mc : Nat),
        (((if f then m0 ^^^ mc else 65535 ^^^ (m0 ^^^ mc)) >>> r.val) &&& 1) =
        if f then (((m0 >>> r.val) &&& 1) ^^^ ((mc >>> r.val) &&& 1))
             else 1 - (((m0 >>> r.val) &&& 1) ^^^ ((mc >>> r.val) &&& 1)) := by
      intro f mc
      cases f
      · simp [hnot_bit, hxor_bit]
      · simp [hxor_bit]
    rw [hsel f1 m1, hsel f2 m2, hsel f3 m3, hs1, hs2, hs3]
    change (if f1 then ((m0 >>> r.val) &&& 1) ^^^ ((m1 >>> r.val) &&& 1) else 1 - (((m0 >>> r.val) &&& 1) ^^^ ((m1 >>> r.val) &&& 1))) &&&
           (if f2 then ((m0 >>> r.val) &&& 1) ^^^ ((m2 >>> r.val) &&& 1) else 1 - (((m0 >>> r.val) &&& 1) ^^^ ((m2 >>> r.val) &&& 1))) &&&
           (if f3 then ((m0 >>> r.val) &&& 1) ^^^ ((m3 >>> r.val) &&& 1) else 1 - (((m0 >>> r.val) &&& 1) ^^^ ((m3 >>> r.val) &&& 1))) =
           if ((if (m0 >>> r.val) &&& 1 = 1 then -1 else 1) +
               (if f1 then -1 else 1) * (if (m1 >>> r.val) &&& 1 = 1 then -1 else 1) +
               (if f2 then -1 else 1) * (if (m2 >>> r.val) &&& 1 = 1 then -1 else 1) +
               (if f3 then -1 else 1) * (if (m3 >>> r.val) &&& 1 = 1 then -1 else 1)).natAbs = 4 then 1 else 0
    rcases nat_and1_cases (m0 >>> r.val) with h0 | h0 <;>
    rcases nat_and1_cases (m1 >>> r.val) with h1 | h1 <;>
    rcases nat_and1_cases (m2 >>> r.val) with h2 | h2 <;>
    rcases nat_and1_cases (m3 >>> r.val) with h3 | h3 <;>
    cases f1 <;> cases f2 <;> cases f3 <;>
    simp [h0, h1, h2, h3]
  have b0 := hbucket false false false 1 1 1 rfl rfl rfl
  have b1 := hbucket true  false false (-1) 1 1 rfl rfl rfl
  have b2 := hbucket false true  false 1 (-1) 1 rfl rfl rfl
  have b3 := hbucket true  true  false (-1) (-1) 1 rfl rfl rfl
  have b4 := hbucket false false true  1 1 (-1) rfl rfl rfl
  have b5 := hbucket true  false true  (-1) 1 (-1) rfl rfl rfl
  have b6 := hbucket false true  true  1 (-1) (-1) rfl rfl rfl
  have b7 := hbucket true  true  true  (-1) (-1) (-1) rfl rfl rfl
  simp only [Bool.false_eq_true, ↓reduceIte] at b0 b1 b2 b3 b4 b5 b6 b7
  unfold maxC4FromMasks16 maxC4
  dsimp only
  rw [b0, b1, b2, b3, b4, b5, b6, b7]

theorem countClosedQuads16Fast_eq (masks : Array Nat) :
    countClosedQuads16Fast masks = countClosedQuads16 (matFromColMasks16 masks) := by
  unfold countClosedQuads16Fast countClosedQuads16
  apply foldFin_congr; intro c0 acc0
  apply foldFin_congr; intro c1 acc1
  split
  · apply foldFin_congr; intro c2 acc2
    split
    · apply foldFin_congr; intro c3 acc3
      rw [maxC4FromMasks16_eq]
    · rfl
  · rfl

set_option maxRecDepth 200000 in
theorem hall16_I_k4_count   : countClosedQuads16 hall16_I   = 140 := by
  rw [hall16_I, ← countClosedQuads16Fast_eq]; decide
set_option maxRecDepth 200000 in
theorem hall16_II_k4_count  : countClosedQuads16 hall16_II  = 76  := by
  rw [hall16_II, ← countClosedQuads16Fast_eq]; decide
set_option maxRecDepth 200000 in
theorem hall16_III_k4_count : countClosedQuads16 hall16_III = 44  := by
  rw [hall16_III, ← countClosedQuads16Fast_eq]; decide
set_option maxRecDepth 200000 in
theorem hall16_IV_k4_count  : countClosedQuads16 hall16_IV  = 28  := by
  rw [hall16_IV, ← countClosedQuads16Fast_eq]; decide
set_option maxRecDepth 200000 in
theorem hall16_V_k4_count   : countClosedQuads16 hall16_V   = 28  := by
  rw [hall16_V, ← countClosedQuads16Fast_eq]; decide

/-! ### 4. Universal Row-Pair Characterization of `hasDoublePeak8Mask16` -/

theorem rowPairAgreeMask16_lt (H : IntMat 16 16) (r1 r2 : Fin 16) :
    rowPairAgreeMask16 H r1 r2 < 65536 := by
  unfold rowPairAgreeMask16
  apply foldFin_invariant (fun a => a < 65536) _ 0 (by omega)
  intro j a ha
  by_cases h : H r1 j = H r2 j
  · simp only [h, ↓reduceIte]
    have hbit : ∀ k : Fin 16, 1 <<< k.val < 65536 := by decide
    exact Nat.or_lt_two_pow (n := 16) ha (hbit j)
  · simp [h, ha]

theorem nat_and1_or (a b : Nat) : (a ||| b) &&& 1 = (a &&& 1) ||| (b &&& 1) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_or]
  cases a.testBit i <;> cases b.testBit i <;> cases (1 : Nat).testBit i <;> rfl

theorem rowPairAgreeMask16_bit (H : IntMat 16 16) (r1 r2 j : Fin 16) :
    ((rowPairAgreeMask16 H r1 r2 >>> j.val) &&& 1 = 1) ↔ H r1 j = H r2 j := by
  have hfold : ∀ (n : Nat) (f : Fin n → Bool) (acc : Nat),
      ((foldFin n (fun i a => if f i then a ||| (1 <<< i.val) else a) acc >>> j.val) &&& 1 = 1) ↔
      (((acc >>> j.val) &&& 1 = 1) ∨ ∃ i : Fin n, i.val = j.val ∧ f i = true) := by
    intro n
    induction n with
    | zero =>
      intro f acc; simp only [foldFin]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨i, _⟩); exact h; exact Fin.elim0 i
    | succ k ih =>
      intro f acc
      simp only [foldFin, Fin.val_castSucc, Fin.val_last]
      rw [ih (fun i => f i.castSucc)]
      have hlast : (((if f (Fin.last k) then acc ||| (1 <<< k) else acc) >>> j.val) &&& 1 = 1) ↔
                   (((acc >>> j.val) &&& 1 = 1) ∨ (k = j.val ∧ f (Fin.last k) = true)) := by
        by_cases hf : f (Fin.last k) = true
        · simp only [hf, ↓reduceIte]
          rw [Nat.shiftRight_or_distrib, nat_and1_or]
          have h1 : (((1 <<< k) >>> j.val) &&& 1 = 1) ↔ k = j.val := by
            by_cases hk : k < 16
            · have hdec : ∀ a b : Fin 16, (((1 <<< a.val) >>> b.val) &&& 1 = 1) ↔ a.val = b.val := by decide
              exact hdec ⟨k, hk⟩ j
            · constructor
              · intro h
                have : (1 <<< k) >>> j.val = 1 <<< (k - j.val) := by
                  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
                  have hlt : j.val < k := by have := j.isLt; omega
                  have hpow : 2 ^ k = 2 ^ (k - j.val) * 2 ^ j.val := by
                    rw [← Nat.pow_add]; congr 1; omega
                  rw [Nat.one_mul, hpow, Nat.mul_div_cancel _ (Nat.two_pow_pos _), Nat.shiftLeft_eq, Nat.one_mul]
                rw [this, Nat.and_one_is_mod, Nat.shiftLeft_eq, Nat.one_mul] at h
                have hgt0 : 0 < k - j.val := by have := j.isLt; omega
                have heven : 2 ^ (k - j.val) % 2 = 0 := by
                  have : 2 ^ (k - j.val) = 2 * 2 ^ (k - j.val - 1) := by
                    rw [← Nat.pow_succ']; congr 1; omega
                  rw [this]; omega
                omega
              · intro heq; have := j.isLt; omega
          rcases nat_and1_cases (acc >>> j.val) with ha | ha <;>
          rcases nat_and1_cases ((1 <<< k) >>> j.val) with hb | hb <;>
          simp [← h1, ha, hb]
        · simp only [hf, Bool.false_eq_true, ↓reduceIte, and_false, or_false]
      rw [hlast]
      constructor
      · rintro ((h | ⟨hk, hfk⟩) | ⟨i, hi, hfi⟩)
        · exact Or.inl h
        · exact Or.inr ⟨Fin.last k, hk, hfk⟩
        · exact Or.inr ⟨i.castSucc, hi, hfi⟩
      · rintro (h | ⟨i, hi, hfi⟩)
        · exact Or.inl (Or.inl h)
        · by_cases hl : i = Fin.last k
          · subst hl; exact Or.inl (Or.inr ⟨hi, hfi⟩)
          · have hlt : i.val < k := by
              have := i.isLt; have hne : i.val ≠ k := fun hv => hl (Fin.ext hv); omega
            exact Or.inr ⟨⟨i.val, hlt⟩, hi, hfi⟩
  unfold rowPairAgreeMask16
  have h := hfold 16 (fun i => decide (H r1 i = H r2 i)) 0
  have hcongr : foldFin 16 (fun i a => if H r1 i = H r2 i then a ||| (1 <<< i.val) else a) 0 =
                foldFin 16 (fun i a => if decide (H r1 i = H r2 i) then a ||| (1 <<< i.val) else a) 0 :=
    foldFin_congr _ _ 0 (fun i a => by by_cases h' : H r1 i = H r2 i <;> simp [h'])
  rw [hcongr, h]
  simp only [Nat.zero_shiftRight, Nat.zero_and, Nat.zero_ne_one, false_or, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, heq⟩; have : i = j := Fin.ext hi; rw [← this]; exact heq
  · intro heq; exact ⟨j, rfl, heq⟩

theorem mem_rowPairMasks16_iff (H : IntMat 16 16) (m : Nat) :
    m ∈ rowPairMasks16 H ↔
    ∃ r1 r2 : Fin 16, r1 < r2 ∧
      (m = rowPairAgreeMask16 H r1 r2 ∨ m = 65535 ^^^ rowPairAgreeMask16 H r1 r2) := by
  have hadd_mem : ∀ (a : Nat) (l : List Nat), (m ∈ if a ∈ l then l else a :: l) ↔ (m = a ∨ m ∈ l) := by
    intro a l
    by_cases ha : a ∈ l
    · simp only [ha, ↓reduceIte]; constructor
      · intro hm; exact Or.inr hm
      · rintro (rfl | hm); exact ha; exact hm
    · simp [ha]
  have hinner : ∀ (n : Nat) (P : Fin n → Prop) [DecidablePred P] (f g : Fin n → Nat) (acc : List Nat),
      (m ∈ foldFin n (fun i a =>
        if P i then
          let a' := if f i ∈ a then a else f i :: a
          if g i ∈ a' then a' else g i :: a'
        else a) acc) ↔
      (m ∈ acc ∨ ∃ i : Fin n, P i ∧ (m = f i ∨ m = g i)) := by
    intro n
    induction n with
    | zero =>
      intro P _ f g acc; simp only [foldFin]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨i, _⟩); exact h; exact Fin.elim0 i
    | succ k ih =>
      intro P _ f g acc
      simp only [foldFin]
      rw [ih (fun i => P i.castSucc) (fun i => f i.castSucc) (fun i => g i.castSucc)]
      have hstep : (m ∈ if P (Fin.last k) then
                          let a' := if f (Fin.last k) ∈ acc then acc else f (Fin.last k) :: acc
                          if g (Fin.last k) ∈ a' then a' else g (Fin.last k) :: a'
                        else acc) ↔
                   (m ∈ acc ∨ (P (Fin.last k) ∧ (m = f (Fin.last k) ∨ m = g (Fin.last k)))) := by
        by_cases hp : P (Fin.last k)
        · simp only [hp, ↓reduceIte, true_and]
          rw [hadd_mem, hadd_mem]
          constructor
          · rintro (h | h | h)
            · exact Or.inr (Or.inr h)
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
          · rintro (h | h | h)
            · exact Or.inr (Or.inr h)
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
        · simp [hp]
      rw [hstep]
      constructor
      · rintro ((hacc | ⟨hp, hfg⟩) | ⟨i, hp, hfg⟩)
        · exact Or.inl hacc
        · exact Or.inr ⟨Fin.last k, hp, hfg⟩
        · exact Or.inr ⟨i.castSucc, hp, hfg⟩
      · rintro (hacc | ⟨i, hp, hfg⟩)
        · exact Or.inl (Or.inl hacc)
        · by_cases hl : i = Fin.last k
          · subst hl; exact Or.inl (Or.inr ⟨hp, hfg⟩)
          · have hlt : i.val < k := by
              have := i.isLt; have hne : i.val ≠ k := fun hv => hl (Fin.ext hv); omega
            exact Or.inr ⟨⟨i.val, hlt⟩, hp, hfg⟩
  have houter : ∀ (n : Nat) (Q : Fin n → List Nat → List Nat) (R : Fin n → Prop) (acc : List Nat),
      (∀ i a, (m ∈ Q i a) ↔ (m ∈ a ∨ R i)) →
      ((m ∈ foldFin n Q acc) ↔ (m ∈ acc ∨ ∃ i : Fin n, R i)) := by
    intro n
    induction n with
    | zero =>
      intro Q R acc _; simp only [foldFin]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨i, _⟩); exact h; exact Fin.elim0 i
    | succ k ih =>
      intro Q R acc hQ
      simp only [foldFin]
      rw [ih (fun i a => Q i.castSucc a) (fun i => R i.castSucc) _ (fun i a => hQ i.castSucc a)]
      rw [hQ (Fin.last k) acc]
      constructor
      · rintro ((hacc | hr) | ⟨i, hr⟩)
        · exact Or.inl hacc
        · exact Or.inr ⟨Fin.last k, hr⟩
        · exact Or.inr ⟨i.castSucc, hr⟩
      · rintro (hacc | ⟨i, hr⟩)
        · exact Or.inl (Or.inl hacc)
        · by_cases hl : i = Fin.last k
          · subst hl; exact Or.inl (Or.inr hr)
          · have hlt : i.val < k := by
              have := i.isLt; have hne : i.val ≠ k := fun hv => hl (Fin.ext hv); omega
            exact Or.inr ⟨⟨i.val, hlt⟩, hr⟩
  unfold rowPairMasks16
  rw [houter 16 _ (fun r1 => ∃ r2 : Fin 16, r1.val < r2.val ∧
        (m = rowPairAgreeMask16 H r1 r2 ∨ m = 65535 ^^^ rowPairAgreeMask16 H r1 r2)) []
        (fun r1 a => hinner 16 (fun r2 => r1.val < r2.val)
          (fun r2 => rowPairAgreeMask16 H r1 r2)
          (fun r2 => 65535 ^^^ rowPairAgreeMask16 H r1 r2) a)]
  simp only [List.not_mem_nil, false_or]
  rfl

theorem hadamard16_row_agree_8 (H : IntMat 16 16)
    (hpm : ∀ r c : Fin 16, H r c = 1 ∨ H r c = -1)
    (hHUt : isOrthogonal (transpose H) 16)
    (r1 r2 : Fin 16) (hne : r1 ≠ r2) :
    sumFinNat 16 (fun j => if H r1 j = H r2 j then 1 else 0) = 8 ∧
    sumFinNat 16 (fun j => if H r1 j ≠ H r2 j then 1 else 0) = 8 := by
  let a := sumFinNat 16 (fun j => if H r1 j = H r2 j then 1 else 0)
  let b := sumFinNat 16 (fun j => if H r1 j ≠ H r2 j then 1 else 0)
  have hab : a + b = 16 := by
    dsimp only [a, b]
    rw [← sumFinNat_add]
    have h1 : sumFinNat 16 (fun j => (if H r1 j = H r2 j then 1 else 0) + (if H r1 j ≠ H r2 j then 1 else 0)) =
              sumFinNat 16 (fun _ => 1) := by
      apply sumFinNat_congr; intro j; by_cases h : H r1 j = H r2 j <;> simp [h]
    rw [h1]; decide
  have hdot : sumFinInt 16 (fun j => H r1 j * H r2 j) = 0 := by
    have h := congrFun (congrFun hHUt r1) r2
    simp only [matMul, transpose, scaleMat, idMat, hne, ↓reduceIte] at h
    omega
  have hdiff : sumFinInt 16 (fun j => H r1 j * H r2 j) = (a : Int) - (b : Int) := by
    dsimp only [a, b]; rw [sumFinNat_toInt, sumFinNat_toInt]
    have hadd := sumFinInt_add
      (fun j : Fin 16 => H r1 j * H r2 j)
      (fun j : Fin 16 => ((if H r1 j ≠ H r2 j then 1 else 0 : Nat) : Int))
    have hc : sumFinInt 16 (fun j : Fin 16 => H r1 j * H r2 j + ((if H r1 j ≠ H r2 j then 1 else 0 : Nat) : Int)) =
              sumFinInt 16 (fun j : Fin 16 => ((if H r1 j = H r2 j then 1 else 0 : Nat) : Int)) := by
      apply sumFinInt_congr; intro j
      rcases hpm r1 j with h1 | h1 <;> rcases hpm r2 j with h2 | h2 <;> simp [h1, h2]
    omega
  omega

theorem eq_of_bits16_eq {a b : Nat} (ha : a < 65536) (hb : b < 65536)
    (h : ∀ j : Fin 16, ((a >>> j.val) &&& 1 = 1) ↔ ((b >>> j.val) &&& 1 = 1)) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 16
  · have hj := h ⟨i, hi⟩
    have htb : ∀ n : Nat, n.testBit i = true ↔ ((n >>> i) &&& 1 = 1) := by
      intro n
      rw [Nat.testBit, Nat.and_one_is_mod]
      constructor
      · intro ht
        cases hmod : (n >>> i) % 2 with
        | zero => simp [hmod] at ht
        | succ k =>
          have : (n >>> i) % 2 < 2 := Nat.mod_lt _ (by omega)
          omega
      · intro h1; simp [h1]
    cases hta : a.testBit i <;> cases htb' : b.testBit i
    · rfl
    · exact absurd ((htb a).mpr (hj.mpr ((htb b).mp htb'))) (by simp [hta])
    · exact absurd ((htb b).mpr (hj.mp ((htb a).mp hta))) (by simp [htb'])
    · rfl
  · have hpow : 65536 ≤ 2 ^ i := by
      have h16 : 2 ^ 16 = 65536 := by decide
      rw [← h16]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hta : a.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha hpow)
    have htb : b.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb hpow)
    rw [hta, htb]

theorem count_ge_2_exists {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (h : 2 ≤ sumFinNat n (fun i => if P i then 1 else 0)) :
    ∃ r1 r2 : Fin n, r1 < r2 ∧ P r1 ∧ P r2 := by
  rcases count_ge_1_exists P (by omega) with ⟨a, hpa⟩
  have s0 := sumFinNat_eq_single_add (fun i => if P i then 1 else 0) a
  simp only [hpa, ↓reduceIte] at s0
  let P1 : Fin n → Prop := fun i => i ≠ a ∧ P i
  have hc1 : sumFinNat n (fun i => if i = a then 0 else if P i then 1 else 0) =
             sumFinNat n (fun i => if P1 i then 1 else 0) :=
    sumFinNat_congr _ _ (fun i => by by_cases hi : i = a <;> simp [P1, hi])
  rcases count_ge_1_exists P1 (by omega) with ⟨b, hba, hpb⟩
  by_cases hab : a < b
  · exact ⟨a, b, hab, hpa, hpb⟩
  · have hlt : b < a := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hab) (fun hv => hba (Fin.ext hv))
    exact ⟨b, a, hlt, hpb, hpa⟩

theorem hasDoublePeak8Mask16_iff_mem_rowPairMasks16 (H : IntMat 16 16)
    (hpm : ∀ r c : Fin 16, H r c = 1 ∨ H r c = -1)
    (hHUt : isOrthogonal (transpose H) 16) (m : Nat) :
    hasDoublePeak8Mask16 H m ↔ m ∈ rowPairMasks16 H := by
  rw [mem_rowPairMasks16_iff]
  constructor
  · rintro ⟨hm_lt, x, hx, hsupp, hcount⟩
    rcases count_ge_2_exists (fun r => (matVec H x r).natAbs = 8) hcount with ⟨r1, r2, hr12, hp1, hp2⟩
    have halign : ∀ r : Fin 16, (matVec H x r).natAbs = 8 →
        ∃ s : Int, (s = 1 ∨ s = -1) ∧ ∀ j : Fin 16, x j ≠ 0 → H r j = s * x j := by
      intro r hpr
      have hpos : ∀ s : Int, (s = 1 ∨ s = -1) → matVec H x r = s * 8 →
          ∀ j0 : Fin 16, x j0 ≠ 0 → H r j0 = s * x j0 := by
        intro s hs hval j0 hj0
        have hsum8 : sumFinInt 16 (fun j => s * (H r j * x j)) = 8 := by
          rw [sumFinInt_mul_left]; change s * matVec H x r = 8; rw [hval]
          rcases hs with rfl | rfl <;> omega
        have hterm_le : ∀ j : Fin 16, s * (H r j * x j) ≤ (if x j = 0 then 0 else 1) := by
          intro j; rcases hs with rfl | rfl <;> rcases hpm r j with hp | hp <;>
          rcases hx.1 j with h0 | h0 | h0 <;> simp [hp, h0]
        have hterm_eq : s * (H r j0 * x j0) = 1 := by
          apply Classical.byContradiction
          intro hne
          have hneg1 : s * (H r j0 * x j0) ≤ -1 := by
            rcases hs with rfl | rfl <;> rcases hpm r j0 with hp | hp <;>
            rcases hx.1 j0 with h0 | h0 | h0 <;> simp_all
          have hle := sumFinInt_le (fun j => s * (H r j * x j))
            (fun j => if j = j0 then -1 else if x j = 0 then 0 else 1)
            (fun j => by by_cases h : j = j0; subst h; simp [hneg1]; simp [h, hterm_le j])
          have h8 : sumFinInt 16 (fun j => if x j = 0 then (0 : Int) else 1) = 8 := by
            have h := sumFinNat_toInt (fun j : Fin 16 => if x j = 0 then 0 else 1)
            rw [hx.2] at h
            have hcongr : sumFinInt 16 (fun j => if x j = 0 then (0 : Int) else 1) =
                          sumFinInt 16 (fun j => ((if x j = 0 then 0 else 1 : Nat) : Int)) :=
              sumFinInt_congr _ _ (fun j => by split <;> rfl)
            rw [hcongr, ← h]; rfl
          have hdiff : sumFinInt 16 (fun j => (if j = j0 then -1 else if x j = 0 then 0 else 1) +
                                              (if j = j0 then (2 : Int) else 0)) =
                       sumFinInt 16 (fun j => if x j = 0 then (0 : Int) else 1) := by
            apply sumFinInt_congr; intro j; by_cases h : j = j0
            · subst h; simp [hj0]
            · simp [h]
          have h2 : sumFinInt 16 (fun j => if j = j0 then (2 : Int) else 0) = 2 := by
            have hsng : ∀ k : Fin 16, sumFinInt 16 (fun j => if j = k then (2 : Int) else 0) = 2 := by decide
            exact hsng j0
          rw [sumFinInt_add, h2, h8] at hdiff
          omega
        rcases hs with rfl | rfl <;> rcases hpm r j0 with hp | hp <;>
        rcases hx.1 j0 with h0 | h0 | h0 <;> simp_all
      rcases int_eq_of_natAbs_eq hpr with h8 | hm8
      · exact ⟨1, Or.inl rfl, hpos 1 (Or.inl rfl) (by omega)⟩
      · exact ⟨-1, Or.inr rfl, hpos (-1) (Or.inr rfl) (by omega)⟩
    rcases halign r1 hp1 with ⟨s1, hs1, ha1⟩
    rcases halign r2 hp2 with ⟨s2, hs2, ha2⟩
    have hne12 : r1 ≠ r2 := fun h => Nat.ne_of_lt hr12 (congrArg Fin.val h)
    have h88 := hadamard16_row_agree_8 H hpm hHUt r1 r2 hne12
    have hsub_eq : ∀ (P Q : Fin 16 → Prop) [DecidablePred P] [DecidablePred Q],
        (∀ j, P j → Q j) →
        sumFinNat 16 (fun j => if P j then 1 else 0) = sumFinNat 16 (fun j => if Q j then 1 else 0) →
        ∀ j, P j ↔ Q j := by
      intro P Q _ _ himp heq j0
      constructor
      · exact himp j0
      · intro hq
        apply Classical.byContradiction
        intro hnp
        have sP := sumFinNat_eq_single_add (fun j => if P j then 1 else 0) j0
        have sQ := sumFinNat_eq_single_add (fun j => if Q j then 1 else 0) j0
        simp only [hnp, hq, ↓reduceIte] at sP sQ
        have hle := sumFinNat_le
          (fun j => if j = j0 then 0 else if P j then 1 else 0)
          (fun j => if j = j0 then 0 else if Q j then 1 else 0)
          (fun j => by
            by_cases h : j = j0
            · simp [h]
            · simp only [h, ↓reduceIte]
              by_cases hp : P j
              · simp [hp, himp j hp]
              · simp [hp])
        omega
    refine ⟨r1, r2, hr12, ?_⟩
    by_cases hs : s1 = s2
    · left
      have hiff : ∀ j : Fin 16, x j ≠ 0 ↔ H r1 j = H r2 j :=
        hsub_eq (fun j => x j ≠ 0) (fun j => H r1 j = H r2 j)
          (fun j hj => by rw [ha1 j hj, ha2 j hj, hs])
          (by
            have h1 : sumFinNat 16 (fun j => if x j ≠ 0 then 1 else 0) = 8 := by
              rw [← hx.2]; apply sumFinNat_congr; intro j; by_cases h : x j = 0 <;> simp [h]
            rw [h1, h88.1])
      apply eq_of_bits16_eq hm_lt (rowPairAgreeMask16_lt H r1 r2)
      intro j
      rw [rowPairAgreeMask16_bit, ← hiff j, ← hsupp j]
    · right
      have hs_neg : s2 = -s1 := by rcases hs1 with rfl | rfl <;> rcases hs2 with rfl | rfl <;> simp_all
      have hiff : ∀ j : Fin 16, x j ≠ 0 ↔ H r1 j ≠ H r2 j :=
        hsub_eq (fun j => x j ≠ 0) (fun j => H r1 j ≠ H r2 j)
          (fun j hj => by
            rw [ha1 j hj, ha2 j hj, hs_neg]
            rcases hs1 with rfl | rfl <;> rcases hx.1 j with h0 | h0 | h0 <;> simp_all)
          (by
            have h1 : sumFinNat 16 (fun j => if x j ≠ 0 then 1 else 0) = 8 := by
              rw [← hx.2]; apply sumFinNat_congr; intro j; by_cases h : x j = 0 <;> simp [h]
            rw [h1, h88.2])
      have hmc_lt : 65535 ^^^ rowPairAgreeMask16 H r1 r2 < 65536 :=
        Nat.xor_lt_two_pow (n := 16) (by omega) (rowPairAgreeMask16_lt H r1 r2)
      apply eq_of_bits16_eq hm_lt hmc_lt
      intro j
      have hxor_bit : (((65535 ^^^ rowPairAgreeMask16 H r1 r2) >>> j.val) &&& 1 = 1) ↔
                      ¬ (((rowPairAgreeMask16 H r1 r2) >>> j.val) &&& 1 = 1) := by
        rw [Nat.shiftRight_xor_distrib, nat_and1_xor]
        have hones : ∀ k : Fin 16, (65535 >>> k.val) &&& 1 = 1 := by decide
        rw [hones j]
        rcases nat_and1_cases (rowPairAgreeMask16 H r1 r2 >>> j.val) with h | h <;> simp [h]
      rw [hxor_bit, rowPairAgreeMask16_bit]
      exact (hsupp j).symm.trans (hiff j)
  · rintro ⟨r1, r2, hr12, hm_eq⟩
    have hne12 : r1 ≠ r2 := fun h => Nat.ne_of_lt hr12 (congrArg Fin.val h)
    have h88 := hadamard16_row_agree_8 H hpm hHUt r1 r2 hne12
    have h8abs : (8 : Int).natAbs = 8 := rfl
    have hm8abs : (-8 : Int).natAbs = 8 := rfl
    rcases hm_eq with rfl | rfl
    · refine ⟨rowPairAgreeMask16_lt H r1 r2, fun j => if H r1 j = H r2 j then H r1 j else 0, ?_, ?_, ?_⟩
      · constructor
        · intro j
          rcases hpm r1 j with h1 | h1 <;> rcases hpm r2 j with h2 | h2 <;> simp [h1, h2]
        · rw [← h88.1]; apply sumFinNat_congr; intro j
          rcases hpm r1 j with h1 | h1 <;> rcases hpm r2 j with h2 | h2 <;> simp [h1, h2]
      · intro j; rw [rowPairAgreeMask16_bit]
        rcases hpm r1 j with h1 | h1 <;> rcases hpm r2 j with h2 | h2 <;> simp [h1, h2]
      · have hv1 : matVec H (fun j => if H r1 j = H r2 j then H r1 j else 0) r1 = 8 := by
          unfold matVec
          have hc : sumFinInt 16 (fun j => H r1 j * (if H r1 j = H r2 j then H r1 j else 0)) =
                    sumFinInt 16 (fun j => ((if H r1 j = H r2 j then 1 else 0 : Nat) : Int)) := by
            apply sumFinInt_congr; intro j
            rcases hpm r1 j with h1 | h1 <;> rcases hpm r2 j with h2 | h2 <;> simp [h1, h2]
          rw [hc, ← sumFinNat_toInt, h88.1]; rfl
        have hv2 : matVec H (fun j => if H r1 j = H r2 j then H r1 j else 0) r2 = 8 := by
          unfold matVec
          have hc : sumFinInt 16 (fun j => H r2 j * (if H r1 j = H r2 j then H r1 j else 0)) =
                    sumFinInt 16 (fun j => ((if H r1 j = H r2 j then 1 else 0 : Nat) : Int)) := by
            apply sumFinInt_congr; intro j
            rcases hpm r1 j with h1 | h1 <;> rcases hpm r2 j with h2 | h2 <;> simp [h1, h2]
          rw [hc, ← sumFinNat_toInt, h88.1]; rfl
        unfold countAbsEq
        have s1 := sumFinNat_eq_single_add (fun i => if (matVec H (fun j => if H r1 j = H r2 j then H r1 j else 0) i).natAbs = 8 then 1 else 0) r1
        have s2 := sumFinNat_eq_single_add (fun i => if i = r1 then 0 else if (matVec H (fun j => if H r1 j = H r2 j then H r1 j else 0) i).natAbs = 8 then 1 else 0) r2
        simp only [hv1, hv2, h8abs, Ne.symm hne12, ↓reduceIte] at s1 s2
        omega
    · have hmc_lt : 65535 ^^^ rowPairAgreeMask16 H r1 r2 < 65536 :=
        Nat.xor_lt_two_pow (n := 16) (by omega) (rowPairAgreeMask16_lt H r1 r2)
      refine ⟨hmc_lt, fun j => if H r1 j ≠ H r2 j then H r1 j else 0, ?_, ?_, ?_⟩
      · constructor
        · intro j
          rcases hpm r1 j with h1 | h1 <;> rcases hpm r2 j with h2 | h2 <;> simp [h1, h2]
        · rw [← h88.2]; apply sumFinNat_congr; intro j
          rcases hpm r1 j with h1 | h1 <;> rcases hpm r2 j with h2 | h2 <;> simp [h1, h2]
      · intro j
        have hxor_bit : (((65535 ^^^ rowPairAgreeMask16 H r1 r2) >>> j.val) &&& 1 = 1) ↔
                        ¬ (((rowPairAgreeMask16 H r1 r2) >>> j.val) &&& 1 = 1) := by
          rw [Nat.shiftRight_xor_distrib, nat_and1_xor]
          have hones : ∀ k : Fin 16, (65535 >>> k.val) &&& 1 = 1 := by decide
          rw [hones j]
          rcases nat_and1_cases (rowPairAgreeMask16 H r1 r2 >>> j.val) with h | h <;> simp [h]
        rw [hxor_bit, rowPairAgreeMask16_bit]
        rcases hpm r1 j with h1 | h1 <;> rcases hpm r2 j with h2 | h2 <;> simp [h1, h2]
      · have hv1 : matVec H (fun j => if H r1 j ≠ H r2 j then H r1 j else 0) r1 = 8 := by
          unfold matVec
          have hc : sumFinInt 16 (fun j => H r1 j * (if H r1 j ≠ H r2 j then H r1 j else 0)) =
                    sumFinInt 16 (fun j => ((if H r1 j ≠ H r2 j then 1 else 0 : Nat) : Int)) := by
            apply sumFinInt_congr; intro j
            rcases hpm r1 j with h1 | h1 <;> rcases hpm r2 j with h2 | h2 <;> simp [h1, h2]
          rw [hc, ← sumFinNat_toInt, h88.2]; rfl
        have hv2 : matVec H (fun j => if H r1 j ≠ H r2 j then H r1 j else 0) r2 = -8 := by
          unfold matVec
          have hc : sumFinInt 16 (fun j => H r2 j * (if H r1 j ≠ H r2 j then H r1 j else 0)) =
                    (-1) * sumFinInt 16 (fun j => ((if H r1 j ≠ H r2 j then 1 else 0 : Nat) : Int)) := by
            rw [← sumFinInt_mul_left]
            apply sumFinInt_congr; intro j
            rcases hpm r1 j with h1 | h1 <;> rcases hpm r2 j with h2 | h2 <;> simp [h1, h2]
          rw [hc, ← sumFinNat_toInt, h88.2]; rfl
        unfold countAbsEq
        have s1 := sumFinNat_eq_single_add (fun i => if (matVec H (fun j => if H r1 j ≠ H r2 j then H r1 j else 0) i).natAbs = 8 then 1 else 0) r1
        have s2 := sumFinNat_eq_single_add (fun i => if i = r1 then 0 else if (matVec H (fun j => if H r1 j ≠ H r2 j then H r1 j else 0) i).natAbs = 8 then 1 else 0) r2
        simp only [hv1, hv2, h8abs, hm8abs, Ne.symm hne12, ↓reduceIte] at s1 s2
        omega

theorem hall16_five_classes_orthogonality_and_k4_k8_duality :
    (isOrthogonal hall16_I 16 ∧ isOrthogonal hall16_II 16 ∧ isOrthogonal hall16_III 16 ∧
     isOrthogonal hall16_IV 16 ∧ isOrthogonal hall16_V 16) ∧
    (countClosedQuads16 hall16_I = 140 ∧
     countClosedQuads16 hall16_II = 76 ∧
     countClosedQuads16 hall16_III = 44 ∧
     countClosedQuads16 hall16_IV = 28 ∧
     countClosedQuads16 hall16_V = 28) ∧
    (∀ H : IntMat 16 16,
      (∀ r c : Fin 16, H r c = 1 ∨ H r c = -1) →
      isOrthogonal (transpose H) 16 →
      ∀ m : Nat, hasDoublePeak8Mask16 H m ↔ m ∈ rowPairMasks16 H) ∧
    (countDoublePeak8Subsets16 hall16_I = 30 ∧
     countDoublePeak8Subsets16 hall16_II = 54 ∧
     countDoublePeak8Subsets16 hall16_III = 90 ∧
     countDoublePeak8Subsets16 hall16_V = 114 ∧
     countDoublePeak8Subsets16 hall16_IV = 156) :=
  ⟨⟨hall16_I_orthogonal, hall16_II_orthogonal, hall16_III_orthogonal,
    hall16_IV_orthogonal, hall16_V_orthogonal⟩,
   ⟨hall16_I_k4_count, hall16_II_k4_count, hall16_III_k4_count,
    hall16_IV_k4_count, hall16_V_k4_count⟩,
   hasDoublePeak8Mask16_iff_mem_rowPairMasks16,
   ⟨hall16_I_k8_count, hall16_II_k8_count, hall16_III_k8_count,
    hall16_V_k8_count, hall16_IV_k8_count⟩⟩

end Paley32Mxfp4
