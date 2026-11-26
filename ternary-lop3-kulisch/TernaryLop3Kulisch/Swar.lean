/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TernaryLop3Kulisch.Defs

/-!
# Exact SWAR64 Zero-Carry-Bleed Packing & Ternary / INT2 Dot-Product Theorem

Pure-`Init` (zero Mathlib, zero `native_decide`) proof of Theorem 5
(`swar64_ternary_int2_dot_zero_overflow`):
1. General SWAR64 lane-isolation & zero-carry-bleed theorem (`P * S ≤ 64` and each lane sum `< 2^S`).
2. General operand-offset unbiasing identity for signed dot products.
3. Exact RX 7900 XTX SWAR64 ternary (`P = 6, S = 10, L ≤ 255, Δ = 1`) zero-overflow + tightness at `S = 9`.
4. Exact RX 7900 XTX SWAR64 INT2 (`P = 5, S = 12, L ≤ 455, Δ = 2`) zero-overflow + tightness at `S = 11`.
-/

namespace TernaryLop3Kulisch

/-! ## 1. List Sum & `swarPackNat` Arithmetic Helpers -/

theorem list_map_sum_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

theorem list_map_sum_mul_right {α : Type} (l : List α) (f : α → Nat) (c : Nat) :
    (l.map (fun x => f x * c)).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

theorem list_map_sum_const {α : Type} (l : List α) (c : Nat) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul]
    omega

theorem sumNat_const (L c : Nat) : sumNat (fun _ : Fin L => c) = L * c := by
  unfold sumNat
  rw [list_map_sum_const, List.length_finRange]

theorem list_map_sum_le {α : Type} (l : List α) (f : α → Nat) (B : Nat)
    (hB : ∀ x ∈ l, f x ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha := hB a (List.mem_cons_self ..)
    have ht := ih (fun x hx => hB x (List.mem_cons_of_mem a hx))
    have hmul : (t.length + 1) * B = t.length * B + B := Nat.succ_mul t.length B
    omega

theorem list_map_sum_comm {α β : Type} (l₁ : List α) (l₂ : List β) (f : α → β → Nat) :
    (l₁.map (fun a => (l₂.map (fun b => f a b)).sum)).sum =
    (l₂.map (fun b => (l₁.map (fun a => f a b)).sum)).sum := by
  induction l₁ with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    rw [list_map_sum_const, Nat.mul_zero]
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← list_map_sum_add]

theorem foldl_add_bv64 (l : List (BitVec 64)) (init : BitVec 64) :
    l.foldl (· + ·) init = init + l.foldl (· + ·) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons]
    rw [ih (init + a), ih (0 + a), BitVec.add_assoc]
    have h0 : (0 : BitVec 64) + a = a := BitVec.zero_add a
    rw [h0]

theorem foldl_ofNat_bv64 (l : List Nat) :
    (l.map (BitVec.ofNat 64)).foldl (· + ·) 0 = BitVec.ofNat 64 l.sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.foldl_cons, List.sum_cons]
    rw [foldl_add_bv64, ih, BitVec.ofNat_add]
    have h0 : (0 : BitVec 64) + BitVec.ofNat 64 a = BitVec.ofNat 64 a := BitVec.zero_add _
    rw [h0]

theorem swarDotAcc64_eq_ofNat (P S L : Nat) (a : Fin L → Fin P → Nat) (b : Fin L → Nat) :
    swarDotAcc64 P S L a b =
      BitVec.ofNat 64 (swarPackNat P S (fun p => sumNat (fun k => a k p * b k))) := by
  unfold swarDotAcc64 swarPack64
  have hmap : (List.finRange L).map (fun k => BitVec.ofNat 64 (swarPackNat P S (a k)) * BitVec.ofNat 64 (b k)) =
      ((List.finRange L).map (fun k => swarPackNat P S (a k) * b k)).map (BitVec.ofNat 64) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro k _
    exact (BitVec.ofNat_mul ..).symm
  rw [hmap, foldl_ofNat_bv64]
  congr 1
  unfold swarPackNat sumNat
  have h1 : (List.finRange L).map (fun k => ((List.finRange P).map (fun p => a k p * 2 ^ (p.val * S))).sum * b k) =
      (List.finRange L).map (fun k => ((List.finRange P).map (fun p => a k p * b k * 2 ^ (p.val * S))).sum) := by
    apply List.map_congr_left
    intro k _
    rw [← list_map_sum_mul_right]
    congr 1
    apply List.map_congr_left
    intro p _
    exact Nat.mul_right_comm (a k p) (2 ^ (p.val * S)) (b k)
  rw [h1, list_map_sum_comm]
  congr 1
  apply List.map_congr_left
  intro p _
  exact list_map_sum_mul_right (List.finRange L) (fun k => a k p * b k) (2 ^ (p.val * S))

/-! ## 2. Positional Base-`2^S` Isolation Theorem -/

/-- Partial sum of `f i * 2^(i * S)` for `i = 0 .. k - 1`. -/
def packPrefix (S : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => packPrefix S f k + f k * 2 ^ (k * S)

theorem packPrefix_lt (S : Nat) (f : Nat → Nat) (k : Nat) (hf : ∀ i < k, f i < 2 ^ S) :
    packPrefix S f k < 2 ^ (k * S) := by
  induction k with
  | zero => simp [packPrefix]
  | succ k ih =>
    unfold packPrefix
    have hprev : packPrefix S f k < 2 ^ (k * S) := ih (fun i hi => hf i (Nat.lt_succ_of_lt hi))
    have hfk : f k < 2 ^ S := hf k (Nat.lt_succ_self k)
    have hle : f k + 1 ≤ 2 ^ S := hfk
    have hpow : 2 ^ ((k + 1) * S) = 2 ^ S * 2 ^ (k * S) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.pow_add, Nat.mul_comm]
    have hmul : (f k + 1) * 2 ^ (k * S) ≤ 2 ^ S * 2 ^ (k * S) :=
      Nat.mul_le_mul_right _ hle
    have hexp : (f k + 1) * 2 ^ (k * S) = f k * 2 ^ (k * S) + 2 ^ (k * S) :=
      Nat.succ_mul (f k) (2 ^ (k * S))
    omega

theorem packPrefix_split (S : Nat) (f : Nat → Nat) (p n : Nat) (hp : p < n) :
    ∃ hi : Nat, packPrefix S f n = packPrefix S f p + f p * 2 ^ (p * S) + hi * 2 ^ ((p + 1) * S) := by
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hpm : p = m
    · subst hpm
      refine ⟨0, ?_⟩
      simp [packPrefix]
    · have hlt : p < m := by omega
      rcases ih hlt with ⟨hi, hhi⟩
      have hge : (p + 1) * S ≤ m * S := Nat.mul_le_mul_right S (by omega)
      have hpow : 2 ^ (m * S) = 2 ^ (m * S - (p + 1) * S) * 2 ^ ((p + 1) * S) := by
        rw [← Nat.pow_add, Nat.sub_add_cancel hge]
      refine ⟨hi + f m * 2 ^ (m * S - (p + 1) * S), ?_⟩
      have hstep : packPrefix S f (m + 1) = packPrefix S f m + f m * 2 ^ (m * S) := rfl
      rw [hstep, hhi, hpow, ← Nat.mul_assoc, Nat.add_assoc, ← Nat.add_mul]

theorem swarPackNat_eq_packPrefix (P S : Nat) (v : Fin P → Nat) :
    swarPackNat P S v = packPrefix S (fun i => if h : i < P then v ⟨i, h⟩ else 0) P := by
  unfold swarPackNat sumNat
  suffices hgen : ∀ (k : Nat) (hk : k ≤ P),
      ((List.finRange k).map (fun p => v ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩ * 2 ^ (p.val * S))).sum =
      packPrefix S (fun i => if h : i < P then v ⟨i, h⟩ else 0) k by
    exact hgen P (Nat.le_refl P)
  intro k
  induction k with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    rw [List.finRange_succ_last, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
    rw [List.map_map]
    change ((List.finRange m).map (fun x => v ⟨x.val, Nat.lt_of_lt_of_le x.isLt (Nat.le_of_succ_le hm)⟩ * 2 ^ (x.val * S))).sum +
      v ⟨m, hm⟩ * 2 ^ (m * S) = packPrefix S (fun i => if h : i < P then v ⟨i, h⟩ else 0) (m + 1)
    rw [ih (Nat.le_of_succ_le hm)]
    have hstep : packPrefix S (fun i => if h : i < P then v ⟨i, h⟩ else 0) (m + 1) =
        packPrefix S (fun i => if h : i < P then v ⟨i, h⟩ else 0) m +
        (if h : m < P then v ⟨m, h⟩ else 0) * 2 ^ (m * S) := rfl
    have hm' : m < P := hm
    rw [hstep]
    simp [hm']

theorem swarPackNat_lt (P S : Nat) (v : Fin P → Nat) (hv : ∀ p : Fin P, v p < 2 ^ S) :
    swarPackNat P S v < 2 ^ (P * S) := by
  rw [swarPackNat_eq_packPrefix]
  apply packPrefix_lt
  intro i hi
  simp only [hi, ↓reduceDIte]
  exact hv ⟨i, hi⟩

theorem swarPackNat_extract (P S : Nat) (v : Fin P → Nat) (hv : ∀ p : Fin P, v p < 2 ^ S)
    (p : Fin P) :
    (swarPackNat P S v / 2 ^ (p.val * S)) % 2 ^ S = v p := by
  rw [swarPackNat_eq_packPrefix]
  let f : Nat → Nat := fun i => if h : i < P then v ⟨i, h⟩ else 0
  rcases packPrefix_split S f p.val P p.isLt with ⟨hi, hsplit⟩
  rw [hsplit]
  have hlo : packPrefix S f p.val < 2 ^ (p.val * S) := by
    apply packPrefix_lt
    intro i hi'
    have hiP : i < P := Nat.lt_trans hi' p.isLt
    simp only [f, hiP, ↓reduceDIte]
    exact hv ⟨i, hiP⟩
  have hpow : 2 ^ ((p.val + 1) * S) = 2 ^ S * 2 ^ (p.val * S) := by
    rw [Nat.add_mul, Nat.one_mul, Nat.pow_add, Nat.mul_comm]
  have hpos : 0 < 2 ^ (p.val * S) := Nat.two_pow_pos _
  have hrew : packPrefix S f p.val + f p.val * 2 ^ (p.val * S) + hi * 2 ^ ((p.val + 1) * S) =
      packPrefix S f p.val + (f p.val + hi * 2 ^ S) * 2 ^ (p.val * S) := by
    rw [hpow, Nat.add_mul, Nat.mul_assoc]
    omega
  rw [hrew, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlo, Nat.zero_add]
  rw [Nat.add_mul_mod_self_right]
  have hfp : f p.val = v p := by simp [f, p.isLt]
  rw [hfp]
  exact Nat.mod_eq_of_lt (hv p)

theorem swarExtractLane_eq_div_mod (S : Nat) (acc : BitVec 64) (p : Nat) :
    swarExtractLane S acc p = (acc.toNat / 2 ^ (p * S)) % 2 ^ S := by
  unfold swarExtractLane
  rw [Nat.shiftRight_eq_div_pow]
  have h1 : 1 <<< S = 2 ^ S := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [h1, Nat.and_two_pow_sub_one_eq_mod]

/-- General SWAR64 zero-carry-bleed lane-isolation theorem. -/
theorem swar64_lane_isolation (P S L : Nat) (hPS : P * S ≤ 64)
    (a : Fin L → Fin P → Nat) (b : Fin L → Nat)
    (hbound : ∀ p : Fin P, sumNat (fun k => a k p * b k) < 2 ^ S) :
    ∀ p : Fin P,
      swarExtractLane S (swarDotAcc64 P S L a b) p.val = sumNat (fun k => a k p * b k) := by
  intro p
  rw [swarDotAcc64_eq_ofNat, swarExtractLane_eq_div_mod]
  have hlt : swarPackNat P S (fun q => sumNat (fun k => a k q * b k)) < 2 ^ 64 := by
    have h1 := swarPackNat_lt P S (fun q => sumNat (fun k => a k q * b k)) hbound
    have h2 : 2 ^ (P * S) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hPS
    omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact swarPackNat_extract P S (fun q => sumNat (fun k => a k q * b k)) hbound p

/-! ## 3. Exact Operand-Offset Unbiasing Identity -/

theorem list_int_sum_add {α : Type} (l : List α) (f g : α → Int) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

theorem list_int_sum_mul_left {α : Type} (l : List α) (c : Int) (f : α → Int) :
    (l.map (fun x => c * f x)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih, Int.mul_add]

theorem list_int_sum_const {α : Type} (l : List α) (c : Int) :
    (l.map (fun _ => c)).sum = Int.ofNat l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    have h : Int.ofNat (t.length + 1) = Int.ofNat t.length + 1 := rfl
    rw [h, Int.add_mul, Int.one_mul]
    omega

theorem operand_offset_unbias {L : Nat} (Δ : Int) (a b : Fin L → Int) :
    exactDotInt a b =
      sumInt (fun k => (a k + Δ) * (b k + Δ)) -
      Δ * sumInt (fun k => a k + Δ) -
      Δ * sumInt (fun k => b k + Δ) +
      Int.ofNat L * (Δ * Δ) := by
  unfold exactDotInt sumInt
  have h1 : (List.finRange L).map (fun k => (a k + Δ) * (b k + Δ)) =
      (List.finRange L).map (fun k => a k * b k + (Δ * (a k + Δ) + (Δ * (b k + Δ) + (-(Δ * Δ))))) := by
    apply List.map_congr_left
    intro k _
    have hmul : (a k + Δ) * (b k + Δ) = a k * b k + a k * Δ + Δ * b k + Δ * Δ := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      omega
    have hda : Δ * (a k + Δ) = Δ * a k + Δ * Δ := Int.mul_add Δ (a k) Δ
    have hdb : Δ * (b k + Δ) = Δ * b k + Δ * Δ := Int.mul_add Δ (b k) Δ
    have hcomm : a k * Δ = Δ * a k := Int.mul_comm (a k) Δ
    omega
  rw [h1, list_int_sum_add, list_int_sum_add, list_int_sum_add,
      list_int_sum_mul_left, list_int_sum_mul_left, list_int_sum_const, List.length_finRange]
  have hneg : Int.ofNat L * -(Δ * Δ) = -(Int.ofNat L * (Δ * Δ)) := Int.mul_neg _ _
  omega

theorem ofNat_sumNat {L : Nat} (f : Fin L → Nat) :
    Int.ofNat (sumNat f) = sumInt (fun k => Int.ofNat (f k)) := by
  unfold sumNat sumInt
  induction (List.finRange L) with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have hadd : Int.ofNat (f a + (t.map f).sum) = Int.ofNat (f a) + Int.ofNat (t.map f).sum := rfl
    rw [hadd, ih]

/-! ## 4. Exact RX 7900 XTX SWAR64 Ternary & INT2 Zero-Overflow & Tightness Theorem -/

theorem swar64_ternary_exact (L : Nat) (hL : L ≤ 255)
    (a : Fin L → Fin 6 → Int) (b : Fin L → Int)
    (ha : ∀ k p, IsTernary (a k p)) (hb : ∀ k, IsTernary (b k)) :
    let aTilde : Fin L → Fin 6 → Nat := fun k p => (a k p + 1).toNat
    let bTilde : Fin L → Nat := fun k => (b k + 1).toNat
    let acc := swarDotAcc64 6 10 L aTilde bTilde
    ∀ p : Fin 6,
      Int.ofNat (swarExtractLane 10 acc p.val) -
        sumInt (fun k => a k p + 1) - sumInt (fun k => b k + 1) + Int.ofNat L =
      exactDotInt (fun k => a k p) b := by
  intro aTilde bTilde acc p
  have hbound : ∀ q : Fin 6, sumNat (fun k => aTilde k q * bTilde k) < 2 ^ 10 := by
    intro q
    have hle : sumNat (fun k => aTilde k q * bTilde k) ≤ L * 4 := by
      unfold sumNat
      have h := list_map_sum_le (List.finRange L) (fun k => aTilde k q * bTilde k) 4 (by
        intro k _
        have h1 : aTilde k q ≤ 2 := by
          rcases ha k q with h | h | h <;> simp [aTilde, h]
        have h2 : bTilde k ≤ 2 := by
          rcases hb k with h | h | h <;> simp [bTilde, h]
        exact Nat.mul_le_mul h1 h2)
      rw [List.length_finRange] at h
      exact h
    have h10 : 2 ^ 10 = 1024 := by decide
    omega
  have hiso := swar64_lane_isolation 6 10 L (by decide) aTilde bTilde hbound p
  rw [hiso, ofNat_sumNat]
  have hprod : sumInt (fun k => Int.ofNat (aTilde k p * bTilde k)) =
      sumInt (fun k => (a k p + 1) * (b k + 1)) := by
    unfold sumInt
    congr 1
    apply List.map_congr_left
    intro k _
    have h1 : Int.ofNat (aTilde k p) = a k p + 1 := by
      rcases ha k p with h | h | h <;> simp [aTilde, h]
    have h2 : Int.ofNat (bTilde k) = b k + 1 := by
      rcases hb k with h | h | h <;> simp [bTilde, h]
    have hmul : Int.ofNat (aTilde k p * bTilde k) = Int.ofNat (aTilde k p) * Int.ofNat (bTilde k) := rfl
    rw [hmul, h1, h2]
  rw [hprod]
  have hunb := operand_offset_unbias (1 : Int) (fun k => a k p) b
  simp only [Int.one_mul, Int.mul_one] at hunb
  rw [hunb]

theorem swar64_int2_exact (L : Nat) (hL : L ≤ 455)
    (a : Fin L → Fin 5 → Int) (b : Fin L → Int)
    (ha : ∀ k p, IsInt2 (a k p)) (hb : ∀ k, IsInt2 (b k)) :
    let aTilde : Fin L → Fin 5 → Nat := fun k p => (a k p + 2).toNat
    let bTilde : Fin L → Nat := fun k => (b k + 2).toNat
    let acc := swarDotAcc64 5 12 L aTilde bTilde
    ∀ p : Fin 5,
      Int.ofNat (swarExtractLane 12 acc p.val) -
        2 * sumInt (fun k => a k p + 2) - 2 * sumInt (fun k => b k + 2) + 4 * Int.ofNat L =
      exactDotInt (fun k => a k p) b := by
  intro aTilde bTilde acc p
  have hbound : ∀ q : Fin 5, sumNat (fun k => aTilde k q * bTilde k) < 2 ^ 12 := by
    intro q
    have hle : sumNat (fun k => aTilde k q * bTilde k) ≤ L * 9 := by
      unfold sumNat
      have h := list_map_sum_le (List.finRange L) (fun k => aTilde k q * bTilde k) 9 (by
        intro k _
        have h1 : aTilde k q ≤ 3 := by
          rcases ha k q with h | h | h | h <;> simp [aTilde, h]
        have h2 : bTilde k ≤ 3 := by
          rcases hb k with h | h | h | h <;> simp [bTilde, h]
        exact Nat.mul_le_mul h1 h2)
      rw [List.length_finRange] at h
      exact h
    have h12 : 2 ^ 12 = 4096 := by decide
    omega
  have hiso := swar64_lane_isolation 5 12 L (by decide) aTilde bTilde hbound p
  rw [hiso, ofNat_sumNat]
  have hprod : sumInt (fun k => Int.ofNat (aTilde k p * bTilde k)) =
      sumInt (fun k => (a k p + 2) * (b k + 2)) := by
    unfold sumInt
    congr 1
    apply List.map_congr_left
    intro k _
    have h1 : Int.ofNat (aTilde k p) = a k p + 2 := by
      rcases ha k p with h | h | h | h <;> simp [aTilde, h]
    have h2 : Int.ofNat (bTilde k) = b k + 2 := by
      rcases hb k with h | h | h | h <;> simp [bTilde, h]
    have hmul : Int.ofNat (aTilde k p * bTilde k) = Int.ofNat (aTilde k p) * Int.ofNat (bTilde k) := rfl
    rw [hmul, h1, h2]
  rw [hprod]
  have hunb := operand_offset_unbias (2 : Int) (fun k => a k p) b
  have h4 : Int.ofNat L * (2 * 2) = 4 * Int.ofNat L := by
    rw [Int.mul_comm]
    rfl
  rw [h4] at hunb
  rw [hunb]

theorem swar64_ternary_tight_S9 :
    swarExtractLane 9 (swarDotAcc64 6 9 255 (fun _ _ => 2) (fun _ => 2)) 0 ≠ 1020 := by
  rw [swarDotAcc64_eq_ofNat]
  have hconst : (fun _ : Fin 6 => sumNat (fun _ : Fin 255 => 2 * 2)) = (fun _ => 255 * (2 * 2)) := by
    funext _
    exact sumNat_const 255 (2 * 2)
  rw [hconst]
  decide

theorem swar64_int2_tight_S11 :
    swarExtractLane 11 (swarDotAcc64 5 11 455 (fun _ _ => 3) (fun _ => 3)) 0 ≠ 4095 := by
  rw [swarDotAcc64_eq_ofNat]
  have hconst : (fun _ : Fin 5 => sumNat (fun _ : Fin 455 => 3 * 3)) = (fun _ => 455 * (3 * 3)) := by
    funext _
    exact sumNat_const 455 (3 * 3)
  rw [hconst]
  decide

/-- Headline Theorem 5: Exact SWAR64 lane isolation, operand-offset unbiasing, and zero-carry-bleed
    + tightness laws for RX 7900 XTX ternary (`P=6, S=10, L≤255`) and INT2 (`P=5, S=12, L≤455`). -/
theorem swar64_ternary_int2_dot_zero_overflow :
    (∀ (P S L : Nat), P * S ≤ 64 →
      ∀ (a : Fin L → Fin P → Nat) (b : Fin L → Nat),
        (∀ p : Fin P, sumNat (fun k => a k p * b k) < 2 ^ S) →
        ∀ p : Fin P,
          swarExtractLane S (swarDotAcc64 P S L a b) p.val = sumNat (fun k => a k p * b k)) ∧
    (∀ (L : Nat), L ≤ 255 →
      ∀ (a : Fin L → Fin 6 → Int) (b : Fin L → Int),
        (∀ k p, IsTernary (a k p)) → (∀ k, IsTernary (b k)) →
        let aTilde : Fin L → Fin 6 → Nat := fun k p => (a k p + 1).toNat
        let bTilde : Fin L → Nat := fun k => (b k + 1).toNat
        let acc := swarDotAcc64 6 10 L aTilde bTilde
        ∀ p : Fin 6,
          Int.ofNat (swarExtractLane 10 acc p.val) -
            sumInt (fun k => a k p + 1) - sumInt (fun k => b k + 1) + Int.ofNat L =
          exactDotInt (fun k => a k p) b) ∧
    (swarExtractLane 9 (swarDotAcc64 6 9 255 (fun _ _ => 2) (fun _ => 2)) 0 ≠ 1020) ∧
    (∀ (L : Nat), L ≤ 455 →
      ∀ (a : Fin L → Fin 5 → Int) (b : Fin L → Int),
        (∀ k p, IsInt2 (a k p)) → (∀ k, IsInt2 (b k)) →
        let aTilde : Fin L → Fin 5 → Nat := fun k p => (a k p + 2).toNat
        let bTilde : Fin L → Nat := fun k => (b k + 2).toNat
        let acc := swarDotAcc64 5 12 L aTilde bTilde
        ∀ p : Fin 5,
          Int.ofNat (swarExtractLane 12 acc p.val) -
            2 * sumInt (fun k => a k p + 2) - 2 * sumInt (fun k => b k + 2) + 4 * Int.ofNat L =
          exactDotInt (fun k => a k p) b) ∧
    (swarExtractLane 11 (swarDotAcc64 5 11 455 (fun _ _ => 3) (fun _ => 3)) 0 ≠ 4095) :=
  ⟨swar64_lane_isolation, swar64_ternary_exact, swar64_ternary_tight_S9,
   swar64_int2_exact, swar64_int2_tight_S11⟩

end TernaryLop3Kulisch
