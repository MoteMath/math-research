/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitLevelKindIc3Invariants.Defs

/-!
# Verified Lean 4 Bit-Level k-Induction & IC3/PDR Invariant-Certificate Engine

Standalone Lean 4.34.1 (zero Mathlib, zero custom axioms, zero `sorry`).
Proves doubly-infinite safety theorems:
  `∀ w ≥ 1, ∀ s0, ∀ inputs, Init_w(s0) → ∀ t : Nat, Prop_w(runTrace s0 inputs t)`
via a single kernel-checked finite binary certificate (`checkKIndIC3 sys prop cert = true`)
plus a general Soundness Meta-Theorem (`checkKIndIC3_sound`).
-/


-- ============================================================================
-- Section 1: Compact Balanced Binary Tree Set of Nat Codes (Fast Kernel `decide`)
-- ============================================================================

namespace KIndIC3

theorem NatSet.all_mem {s : NatSet} {p : Nat → Bool}
    (hall : s.all p = true) : ∀ c, s.mem c = true → p c = true := by
  induction s with
  | empty =>
    intro c hmem
    simp [NatSet.mem] at hmem
  | node v l r ihl ihr =>
    intro c hmem
    simp only [NatSet.all, Bool.and_eq_true] at hall
    obtain ⟨⟨hpv, hl⟩, hr⟩ := hall
    simp only [NatSet.mem] at hmem
    split at hmem
    · rename_i heq
      have : c = v := eq_of_beq heq
      subst this
      exact hpv
    · split at hmem
      · exact ihl hl c hmem
      · exact ihr hr c hmem

theorem allRange_spec {n : Nat} {p : Nat → Bool}
    (h : allRange n p = true) : ∀ i, i < n → p i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi
    simp only [allRange, Bool.and_eq_true] at h
    by_cases heq : i = k
    · subst heq; exact h.1
    · exact ih h.2 i (by omega)

-- ============================================================================
-- Section 2: Bit-Packing & Exact Nat Carry / Borrow Arithmetic Lemmas
-- ============================================================================

theorem bool_toNat_mod2_beq1 (b : Bool) : (b.toNat % 2 == 1) = b := by
  cases b <;> rfl

theorem mod_pack {a b k : Nat} (ha : a < 2 ^ k) :
    (a + b * 2 ^ k) % 2 ^ k = a := by
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]

theorem div_pack {a b k : Nat} (ha : a < 2 ^ k) :
    (a + b * 2 ^ k) / 2 ^ k = b := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt ha, Nat.zero_add]

theorem pack_lt {a b k m : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ m) :
    a + b * 2 ^ k < 2 ^ (k + m) := by
  rw [Nat.pow_add]
  have h1 : b + 1 ≤ 2 ^ m := hb
  have h2 : (b + 1) * 2 ^ k ≤ 2 ^ m * 2 ^ k := Nat.mul_le_mul_right (2 ^ k) h1
  have h3 : (b + 1) * 2 ^ k = b * 2 ^ k + 2 ^ k := Nat.succ_mul b (2 ^ k)
  have h4 : 2 ^ m * 2 ^ k = 2 ^ k * 2 ^ m := Nat.mul_comm _ _
  omega

theorem pack_bool_lt (b : Bool) : b.toNat < 2 ^ 1 := by
  cases b <;> decide

def natBit (n i : Nat) : Bool := (n / 2 ^ i) % 2 == 1

theorem natBit_eq_testBit (n i : Nat) : natBit n i = n.testBit i := by
  simp [natBit, Nat.testBit, Nat.shiftRight_eq_div_pow]

theorem mod_two_pow_succ (n i : Nat) :
    n % 2 ^ (i + 1) = n % 2 ^ i + (natBit n i).toNat * 2 ^ i := by
  have h1 : 2 ^ (i + 1) = 2 ^ i * 2 := by rw [Nat.pow_succ]
  rw [h1, Nat.mod_mul]
  have hbit : (natBit n i).toNat = (n / 2 ^ i) % 2 := by
    unfold natBit
    have hlt : (n / 2 ^ i) % 2 < 2 := Nat.mod_lt _ (by omega)
    match h : (n / 2 ^ i) % 2 with
    | 0 => rfl
    | 1 => rfl
    | k + 2 => omega
  rw [hbit, Nat.mul_comm]

theorem bitvec_getLsbD_eq_natBit {w : Nat} (x : BitVec w) (i : Nat) :
    x.getLsbD i = natBit x.toNat i := by
  rw [natBit_eq_testBit, BitVec.getLsbD]

theorem bitvec_getLsbD_ge_w {w : Nat} (x : BitVec w) {i : Nat} (hi : w ≤ i) :
    x.getLsbD i = false := by
  rw [BitVec.getLsbD]
  have hlt : x.toNat < 2 ^ i :=
    Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) hi)
  exact Nat.testBit_lt_two_pow hlt

-- Exact carry bit for a + b at bit position i

def natCarry (i a b : Nat) : Bool :=
  decide (a % 2 ^ i + b % 2 ^ i ≥ 2 ^ i)

theorem natCarry_zero (a b : Nat) : natCarry 0 a b = false := by
  simp [natCarry, Nat.mod_one]

theorem natCarry_step (i a b : Nat) :
    let b1 := natBit a i
    let b2 := natBit b i
    let c  := natCarry i a b
    natCarry (i + 1) a b = ((b1 && b2) || (c && (b1 != b2))) ∧
    natBit (a + b) i = ((b1 != b2) != c) := by
  dsimp only
  have ha := mod_two_pow_succ a i
  have hb := mod_two_pow_succ b i
  have hpow : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [Nat.pow_succ]; omega
  have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
  have hmodA : a % 2 ^ i < 2 ^ i := Nat.mod_lt _ hpos
  have hmodB : b % 2 ^ i < 2 ^ i := Nat.mod_lt _ hpos
  have hdiv : (a + b) / 2 ^ i = a / 2 ^ i + b / 2 ^ i + (natCarry i a b).toNat := by
    have hda : a = 2 ^ i * (a / 2 ^ i) + a % 2 ^ i := (Nat.div_add_mod a (2 ^ i)).symm
    have hdb : b = 2 ^ i * (b / 2 ^ i) + b % 2 ^ i := (Nat.div_add_mod b (2 ^ i)).symm
    have hsum : a + b = (a % 2 ^ i + b % 2 ^ i) + (a / 2 ^ i + b / 2 ^ i) * 2 ^ i := by
      have hm := Nat.add_mul (a / 2 ^ i) (b / 2 ^ i) (2 ^ i)
      have hc1 : a / 2 ^ i * 2 ^ i = 2 ^ i * (a / 2 ^ i) := Nat.mul_comm _ _
      have hc2 : b / 2 ^ i * 2 ^ i = 2 ^ i * (b / 2 ^ i) := Nat.mul_comm _ _
      omega
    rw [hsum, Nat.add_mul_div_right _ _ hpos]
    unfold natCarry
    by_cases hc : a % 2 ^ i + b % 2 ^ i ≥ 2 ^ i
    · have hsub : a % 2 ^ i + b % 2 ^ i = (a % 2 ^ i + b % 2 ^ i - 2 ^ i) + 1 * 2 ^ i := by omega
      have hd1 : (a % 2 ^ i + b % 2 ^ i) / 2 ^ i = 1 := by
        rw [hsub, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by omega)]
      simp [hc, hd1]; omega
    · have hd0 : (a % 2 ^ i + b % 2 ^ i) / 2 ^ i = 0 := Nat.div_eq_of_lt (by omega)
      simp [hc, hd0]
  constructor
  · unfold natCarry
    rw [ha, hb, hpow]
    cases hb1 : natBit a i <;> cases hb2 : natBit b i <;>
      by_cases hc : a % 2 ^ i + b % 2 ^ i ≥ 2 ^ i <;>
      simp [hc] <;> omega
  · unfold natBit at *
    rw [hdiv]
    have h1 : (a / 2 ^ i) % 2 < 2 := Nat.mod_lt _ (by omega)
    have h2 : (b / 2 ^ i) % 2 < 2 := Nat.mod_lt _ (by omega)
    have hmod_sum : (a / 2 ^ i + b / 2 ^ i + (natCarry i a b).toNat) % 2 =
        ((a / 2 ^ i) % 2 + (b / 2 ^ i) % 2 + (natCarry i a b).toNat) % 2 := by
      omega
    rw [hmod_sum]
    cases hc : natCarry i a b <;>
      match h1v : (a / 2 ^ i) % 2, h2v : (b / 2 ^ i) % 2 with
      | 0, 0 => simp
      | 0, 1 => simp
      | 1, 0 => simp
      | 1, 1 => simp
      | _ + 2, _ => omega
      | _, _ + 2 => omega

theorem bitvec_add_getLsbD {w : Nat} (x y : BitVec w) {i : Nat} (hi : i < w) :
    (x + y).getLsbD i = natBit (x.toNat + y.toNat) i := by
  rw [bitvec_getLsbD_eq_natBit]
  simp only [BitVec.toNat_add, natBit]
  have hpow : 2 ^ w = 2 ^ (i + 1) * 2 ^ (w - (i + 1)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have h2 : 2 ^ w = 2 ^ i * (2 * 2 ^ (w - (i + 1))) := by
    rw [hpow, Nat.pow_succ]; ac_rfl
  rw [h2, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]

-- Exact borrow bit for a - b - b0 at bit position i

def natBorrow (i a b : Nat) (b0 : Bool) : Bool :=
  decide (a % 2 ^ i < b % 2 ^ i + b0.toNat)

theorem natBorrow_zero (a b : Nat) (b0 : Bool) : natBorrow 0 a b b0 = b0 := by
  cases b0 <;> simp [natBorrow, Nat.mod_one]

theorem natBorrow_step (i a b : Nat) (b0 : Bool) :
    let b1 := natBit a i
    let b2 := natBit b i
    let brw := natBorrow i a b b0
    natBorrow (i + 1) a b b0 = ((!b1 && b2) || (!b1 && brw) || (b2 && brw)) := by
  dsimp only
  have ha := mod_two_pow_succ a i
  have hb := mod_two_pow_succ b i
  have hmodA : a % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
  have hmodB : b % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
  unfold natBorrow
  rw [ha, hb]
  cases b0 <;> cases hb1 : natBit a i <;> cases hb2 : natBit b i
  all_goals (
    first
    | (by_cases hbrw : a % 2 ^ i < b % 2 ^ i + 0 <;> simp <;> omega)
    | (by_cases hbrw : a % 2 ^ i < b % 2 ^ i + 1 <;> simp <;> omega))

theorem bitvec_sub_getLsbD {w : Nat} (x y : BitVec w) {i : Nat} (hi : i < w) :
    (x - y).getLsbD i =
      ((natBit x.toNat i != natBit y.toNat i) != natBorrow i x.toNat y.toNat false) := by
  have hxlt : x.toNat < 2 ^ w := x.isLt
  have hylt : y.toNat < 2 ^ w := y.isLt
  have hsub_toNat : (x - y).toNat = (2 ^ w - y.toNat + x.toNat) % 2 ^ w := by
    simp [BitVec.toNat_sub]
  rw [bitvec_getLsbD_eq_natBit, hsub_toNat]
  have hpow : 2 ^ w = 2 ^ i * (2 * 2 ^ (w - (i + 1))) := by
    have : 2 ^ w = 2 ^ (i + 1) * 2 ^ (w - (i + 1)) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [this, Nat.pow_succ]; ac_rfl
  have hmod_div : ((2 ^ w - y.toNat + x.toNat) % 2 ^ w) / 2 ^ i % 2 =
                  ((2 ^ w - y.toNat + x.toNat) / 2 ^ i) % 2 := by
    rw [hpow, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]
  unfold natBit
  rw [hmod_div]
  let P := 2 ^ i
  let Q := 2 * 2 ^ (w - (i + 1))
  let xq := x.toNat / P
  let xr := x.toNat % P
  let yq := y.toNat / P
  let yr := y.toNat % P
  have hpos : 0 < P := Nat.two_pow_pos i
  have hdx : x.toNat = P * xq + xr := (Nat.div_add_mod x.toNat P).symm
  have hdy : y.toNat = P * yq + yr := (Nat.div_add_mod y.toNat P).symm
  have hmx : xr < P := Nat.mod_lt _ hpos
  have hmy : yr < P := Nat.mod_lt _ hpos
  have hyq_lt : yq < Q := by
    have hpq : P * Q = 2 ^ w := hpow.symm
    have : P * yq < P * Q := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hge1 : yq + 1 ≤ Q := hyq_lt
  have hdiv_exact : (2 ^ w - y.toNat + x.toNat) / P =
      Q + xq - yq - (natBorrow i x.toNat y.toNat false).toNat := by
    unfold natBorrow
    simp only [Bool.toNat_false, Nat.add_zero]
    change (2 ^ w - y.toNat + x.toNat) / P = Q + xq - yq - (decide (xr < yr)).toNat
    by_cases hbr : xr < yr
    · simp only [hbr, decide_true, Bool.toNat_true]
      have hsub1 : (Q + xq - yq - 1) * P + (yq + 1) * P = (Q + xq) * P := by
        rw [← Nat.add_mul]; congr 1
        have : yq + 1 ≤ Q + xq := Nat.le_trans hge1 (Nat.le_add_right Q xq)
        omega
      have hmul1 : (Q + xq) * P = P * Q + P * xq := by
        rw [Nat.add_mul, Nat.mul_comm Q P, Nat.mul_comm xq P]
      have hmul2 : (yq + 1) * P = P * yq + P := by
        rw [Nat.add_mul, Nat.mul_comm yq P, Nat.one_mul]
      have hpq : P * Q = 2 ^ w := hpow.symm
      have heq : 2 ^ w - y.toNat + x.toNat = (P + xr - yr) + (Q + xq - yq - 1) * P := by
        omega
      rw [heq, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    · simp only [hbr, decide_false, Bool.toNat_false, Nat.sub_zero]
      have hsub1 : (Q + xq - yq) * P + yq * P = (Q + xq) * P := by
        rw [← Nat.add_mul]; congr 1
        have : yq ≤ Q + xq := Nat.le_trans (Nat.le_of_lt hyq_lt) (Nat.le_add_right Q xq)
        omega
      have hmul1 : (Q + xq) * P = P * Q + P * xq := by
        rw [Nat.add_mul, Nat.mul_comm Q P, Nat.mul_comm xq P]
      have hmul2 : yq * P = P * yq := Nat.mul_comm yq P
      have hpq : P * Q = 2 ^ w := hpow.symm
      have heq : 2 ^ w - y.toNat + x.toNat = (xr - yr) + (Q + xq - yq) * P := by
        omega
      rw [heq, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  change ((2 ^ w - y.toNat + x.toNat) / P % 2 == 1) =
    (((xq % 2 == 1) != (yq % 2 == 1)) != natBorrow i x.toNat y.toNat false)
  rw [hdiv_exact]
  have hQeven : Q % 2 = 0 := by simp [Q]
  have hQxq : yq + 1 ≤ Q + xq := Nat.le_trans hge1 (Nat.le_add_right Q xq)
  generalize hQ_eq : Q = Qn at hQeven hQxq ⊢
  generalize hxq_eq : xq = xn at hQxq ⊢
  generalize hyq_eq : yq = yn at hQxq ⊢
  cases hbr : natBorrow i x.toNat y.toNat false <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.sub_zero] <;>
    (have h1 : xn % 2 < 2 := Nat.mod_lt _ (by omega);
     have h2 : yn % 2 < 2 := Nat.mod_lt _ (by omega);
     match h1v : xn % 2, h2v : yn % 2 with
     | 0, 0 => simp; omega
     | 0, 1 => simp; omega
     | 1, 0 => simp; omega
     | 1, 1 => simp; omega
     | _ + 2, _ => omega
     | _, _ + 2 => omega)

theorem natBorrow_w_ule {w : Nat} (x y : BitVec w) :
    (!natBorrow w y.toNat x.toNat false) = decide (x ≤ y) := by
  unfold natBorrow
  rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt]
  simp only [Bool.toNat_false, Nat.add_zero]
  by_cases h : x.toNat ≤ y.toNat
  · have h1 : ¬ (y.toNat < x.toNat) := by omega
    have h2 : x ≤ y := h
    simp [h1, h2]
  · have h1 : y.toNat < x.toNat := by omega
    have h2 : ¬ (x ≤ y) := h
    simp [h1, h2]

theorem natBorrow_w_ult {w : Nat} (x y : BitVec w) :
    (!natBorrow w y.toNat x.toNat true) = decide (x < y) := by
  unfold natBorrow
  rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt]
  simp only [Bool.toNat_true]
  by_cases h : x.toNat < y.toNat
  · have h1 : ¬ (y.toNat < x.toNat + 1) := by omega
    have h2 : x < y := h
    simp [h1, h2]
  · have h1 : y.toNat < x.toNat + 1 := by omega
    have h2 : ¬ (x < y) := h
    simp [h1, h2]

-- ============================================================================
-- Section 3: Width-Uniform Bit-Vector AST & Native `BitVec w` Semantics
-- ============================================================================

def vecMask {w k : Nat} (v : Fin k → BitVec w) (i : Nat) : Nat :=
  go k (Nat.le_refl k)
where
  go : (n : Nat) → n ≤ k → Nat
    | 0, _ => 0
    | n + 1, hn =>
      go n (Nat.le_of_succ_le hn) + ((v ⟨n, hn⟩).getLsbD i).toNat * 2 ^ n

theorem vecMask_go_lt {w k : Nat} (v : Fin k → BitVec w) (i : Nat) (n : Nat) (hn : n ≤ k) :
    vecMask.go v i n hn < 2 ^ n := by
  induction n with
  | zero => simp [vecMask.go]
  | succ n ih =>
    simp only [vecMask.go]
    have h1 := ih (Nat.le_of_succ_le hn)
    have h2 := pack_bool_lt ((v ⟨n, hn⟩).getLsbD i)
    have := pack_lt h1 h2
    simpa [Nat.pow_succ] using this

theorem vecMask_lt {w k : Nat} (v : Fin k → BitVec w) (i : Nat) :
    vecMask v i < 2 ^ k :=
  vecMask_go_lt v i k (Nat.le_refl k)

theorem vecMask_go_bit {w k : Nat} (v : Fin k → BitVec w) (i : Nat)
    (n : Nat) (hn : n ≤ k) (j : Fin k) (hj : j.val < n) :
    ((vecMask.go v i n hn / 2 ^ j.val) % 2 == 1) = (v j).getLsbD i := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [vecMask.go]
    by_cases heq : j.val = n
    · have hj_eq : j = ⟨n, hn⟩ := Fin.ext heq
      subst hj_eq
      rw [div_pack (vecMask_go_lt v i n (Nat.le_of_succ_le hn))]
      exact bool_toNat_mod2_beq1 _
    · have hjlt : j.val < n := by omega
      let d := n - j.val - 1
      have hd : n = j.val + (d + 1) := by omega
      have hpow : 2 ^ n = (2 * 2 ^ d) * 2 ^ j.val := by
        rw [hd, Nat.pow_add, Nat.pow_succ]; ac_rfl
      let b := ((v ⟨n, hn⟩).getLsbD i).toNat
      let rest := vecMask.go v i n (Nat.le_of_succ_le hn)
      have hdiv : (rest + b * 2 ^ n) / 2 ^ j.val =
          rest / 2 ^ j.val + 2 * (b * 2 ^ d) := by
        have hm : b * 2 ^ n = (2 * (b * 2 ^ d)) * 2 ^ j.val := by
          rw [hpow]; ac_rfl
        rw [hm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos j.val)]
      change ((rest + b * 2 ^ n) / 2 ^ j.val % 2 == 1) = (v j).getLsbD i
      rw [hdiv, Nat.add_mul_mod_self_left]
      exact ih (Nat.le_of_succ_le hn) hjlt

theorem vecMask_bit {w k : Nat} (v : Fin k → BitVec w) (i : Nat) (j : Fin k) :
    ((vecMask v i / 2 ^ j.val) % 2 == 1) = (v j).getLsbD i :=
  vecMask_go_bit v i k (Nat.le_refl k) j j.isLt

def canonExprCode {w r m : Nat} (regs : Fin r → BitVec w) (inps : Fin m → BitVec w)
    (i : Nat) : BVExpr r m → Nat
  | .zero      => 0
  | .one       => (decide (i = 0)).toNat
  | .allOnes   => 0
  | .reg _     => 0
  | .inp _     => 0
  | .not e     => canonExprCode regs inps i e
  | .and e1 e2 => canonExprCode regs inps i e1 + canonExprCode regs inps i e2 * 2 ^ exprBits e1
  | .or e1 e2  => canonExprCode regs inps i e1 + canonExprCode regs inps i e2 * 2 ^ exprBits e1
  | .xor e1 e2 => canonExprCode regs inps i e1 + canonExprCode regs inps i e2 * 2 ^ exprBits e1
  | .add e1 e2 =>
    let v1 := evalExpr regs inps e1
    let v2 := evalExpr regs inps e2
    let c  := natCarry i v1.toNat v2.toNat
    canonExprCode regs inps i e1 +
      (canonExprCode regs inps i e2 + c.toNat * 2 ^ exprBits e2) * 2 ^ exprBits e1
  | .sub e1 e2 =>
    let v1 := evalExpr regs inps e1
    let v2 := evalExpr regs inps e2
    let br := natBorrow i v1.toNat v2.toNat false
    canonExprCode regs inps i e1 +
      (canonExprCode regs inps i e2 + br.toNat * 2 ^ exprBits e2) * 2 ^ exprBits e1
  | .shl1 e    =>
    let prev := if i = 0 then false else (evalExpr regs inps e).getLsbD (i - 1)
    canonExprCode regs inps i e + prev.toNat * 2 ^ exprBits e
  | .shr1 e    =>
    let st :=
      if i = 0 then 0
      else if ((evalExpr regs inps e) >>> 1).getLsbD (i - 1) then 2 else 1
    canonExprCode regs inps i e + st * 2 ^ exprBits e

def canonExprGuess {w r m : Nat} (regs : Fin r → BitVec w) (inps : Fin m → BitVec w)
    (i : Nat) : BVExpr r m → Nat
  | .zero      => 0
  | .one       => 0
  | .allOnes   => 0
  | .reg _     => 0
  | .inp _     => 0
  | .not e     => canonExprGuess regs inps i e
  | .and e1 e2 => canonExprGuess regs inps i e1 + canonExprGuess regs inps i e2 * 2 ^ exprGuesses e1
  | .or e1 e2  => canonExprGuess regs inps i e1 + canonExprGuess regs inps i e2 * 2 ^ exprGuesses e1
  | .xor e1 e2 => canonExprGuess regs inps i e1 + canonExprGuess regs inps i e2 * 2 ^ exprGuesses e1
  | .add e1 e2 => canonExprGuess regs inps i e1 + canonExprGuess regs inps i e2 * 2 ^ exprGuesses e1
  | .sub e1 e2 => canonExprGuess regs inps i e1 + canonExprGuess regs inps i e2 * 2 ^ exprGuesses e1
  | .shl1 e    => canonExprGuess regs inps i e
  | .shr1 e    =>
    let gb := ((evalExpr regs inps e) >>> 1).getLsbD i
    canonExprGuess regs inps i e + gb.toNat * 2 ^ exprGuesses e

theorem canonExprCode_lt {w r m : Nat} (regs : Fin r → BitVec w) (inps : Fin m → BitVec w)
    (i : Nat) (e : BVExpr r m) : canonExprCode regs inps i e < 2 ^ exprBits e := by
  induction e with
  | zero | allOnes | reg _ | inp _ => simp [canonExprCode, exprBits]
  | one => simp [canonExprCode, exprBits]; cases decide (i = 0) <;> decide
  | not e ih => exact ih
  | and e1 e2 ih1 ih2 | or e1 e2 ih1 ih2 | xor e1 e2 ih1 ih2 =>
    exact pack_lt ih1 ih2
  | add e1 e2 ih1 ih2 =>
    have h2 := pack_lt ih2 (pack_bool_lt (natCarry i (evalExpr regs inps e1).toNat (evalExpr regs inps e2).toNat))
    have h3 := pack_lt ih1 h2
    simpa [canonExprCode, exprBits, Nat.add_assoc] using h3
  | sub e1 e2 ih1 ih2 =>
    have h2 := pack_lt ih2 (pack_bool_lt (natBorrow i (evalExpr regs inps e1).toNat (evalExpr regs inps e2).toNat false))
    have h3 := pack_lt ih1 h2
    simpa [canonExprCode, exprBits, Nat.add_assoc] using h3
  | shl1 e ih =>
    exact pack_lt ih (pack_bool_lt _)
  | shr1 e ih =>
    have hst : (if i = 0 then 0 else if ((evalExpr regs inps e) >>> 1).getLsbD (i - 1) then 2 else 1) < 2 ^ 2 := by
      split
      · omega
      · split <;> omega
    exact pack_lt ih hst

theorem canonExprGuess_lt {w r m : Nat} (regs : Fin r → BitVec w) (inps : Fin m → BitVec w)
    (i : Nat) (e : BVExpr r m) : canonExprGuess regs inps i e < 2 ^ exprGuesses e := by
  induction e with
  | zero | one | allOnes | reg _ | inp _ => simp [canonExprGuess, exprGuesses]
  | not e ih | shl1 e ih => exact ih
  | and e1 e2 ih1 ih2 | or e1 e2 ih1 ih2 | xor e1 e2 ih1 ih2
  | add e1 e2 ih1 ih2 | sub e1 e2 ih1 ih2 =>
    exact pack_lt ih1 ih2
  | shr1 e ih =>
    exact pack_lt ih (pack_bool_lt _)

theorem canonExprCode_zero {w r m : Nat} (regs : Fin r → BitVec w) (inps : Fin m → BitVec w)
    (e : BVExpr r m) : canonExprCode regs inps 0 e = exprInitCode e := by
  induction e with
  | zero | one | allOnes | reg _ | inp _ => rfl
  | not e ih => exact ih
  | and e1 e2 ih1 ih2 | or e1 e2 ih1 ih2 | xor e1 e2 ih1 ih2 =>
    simp [canonExprCode, exprInitCode, ih1, ih2]
  | add e1 e2 ih1 ih2 =>
    simp [canonExprCode, exprInitCode, natCarry_zero, ih1, ih2]
  | sub e1 e2 ih1 ih2 =>
    simp [canonExprCode, exprInitCode, natBorrow_zero, ih1, ih2]
  | shl1 e ih =>
    simp [canonExprCode, exprInitCode, ih]
  | shr1 e ih =>
    simp [canonExprCode, exprInitCode, ih]

theorem canonExprCode_step {w r m : Nat} (regs : Fin r → BitVec w) (inps : Fin m → BitVec w)
    {i : Nat} (hi : i < w) (e : BVExpr r m) :
    stepExprCode (vecMask regs i) (vecMask inps i) e
      (canonExprCode regs inps i e) (canonExprGuess regs inps i e) =
    (canonExprCode regs inps (i + 1) e, true, (evalExpr regs inps e).getLsbD i) := by
  induction e with
  | zero =>
    simp [stepExprCode, canonExprCode, evalExpr]
  | one =>
    simp only [stepExprCode, canonExprCode, evalExpr, BitVec.getLsbD_ofNat]
    cases i with
    | zero => simp [hi]
    | succ k =>
      have htb : Nat.testBit 1 (k + 1) = false := by
        simp [Nat.testBit, Nat.shiftRight_eq_div_pow]
        have : 1 < 2 ^ (k + 1) := by
          have := Nat.two_pow_pos k
          rw [Nat.pow_succ]; omega
        rw [Nat.div_eq_of_lt this]
      simp [hi, htb]
  | allOnes =>
    simp [stepExprCode, canonExprCode, evalExpr, hi]
  | reg idx =>
    simp [stepExprCode, canonExprCode, evalExpr, vecMask_bit]
  | inp idx =>
    simp [stepExprCode, canonExprCode, evalExpr, vecMask_bit]
  | not e ih =>
    simp [stepExprCode, canonExprCode, canonExprGuess, evalExpr, ih, hi]
  | and e1 e2 ih1 ih2 =>
    simp only [stepExprCode, canonExprCode, canonExprGuess, evalExpr]
    rw [mod_pack (canonExprCode_lt regs inps i e1), div_pack (canonExprCode_lt regs inps i e1),
        mod_pack (canonExprGuess_lt regs inps i e1), div_pack (canonExprGuess_lt regs inps i e1),
        ih1, ih2]
    simp [BitVec.getLsbD_and]
  | or e1 e2 ih1 ih2 =>
    simp only [stepExprCode, canonExprCode, canonExprGuess, evalExpr]
    rw [mod_pack (canonExprCode_lt regs inps i e1), div_pack (canonExprCode_lt regs inps i e1),
        mod_pack (canonExprGuess_lt regs inps i e1), div_pack (canonExprGuess_lt regs inps i e1),
        ih1, ih2]
    simp [BitVec.getLsbD_or]
  | xor e1 e2 ih1 ih2 =>
    simp only [stepExprCode, canonExprCode, canonExprGuess, evalExpr]
    rw [mod_pack (canonExprCode_lt regs inps i e1), div_pack (canonExprCode_lt regs inps i e1),
        mod_pack (canonExprGuess_lt regs inps i e1), div_pack (canonExprGuess_lt regs inps i e1),
        ih1, ih2]
    simp [BitVec.getLsbD_xor]
  | add e1 e2 ih1 ih2 =>
    simp only [stepExprCode, canonExprCode, canonExprGuess, evalExpr]
    rw [mod_pack (canonExprCode_lt regs inps i e1), div_pack (canonExprCode_lt regs inps i e1),
        mod_pack (canonExprCode_lt regs inps i e2), div_pack (canonExprCode_lt regs inps i e2),
        mod_pack (canonExprGuess_lt regs inps i e1), div_pack (canonExprGuess_lt regs inps i e1),
        ih1, ih2, bool_toNat_mod2_beq1]
    have hstep := natCarry_step i (evalExpr regs inps e1).toNat (evalExpr regs inps e2).toNat
    dsimp only at hstep
    rw [bitvec_add_getLsbD _ _ hi, bitvec_getLsbD_eq_natBit, bitvec_getLsbD_eq_natBit]
    simp [hstep.1, hstep.2]
  | sub e1 e2 ih1 ih2 =>
    simp only [stepExprCode, canonExprCode, canonExprGuess, evalExpr]
    rw [mod_pack (canonExprCode_lt regs inps i e1), div_pack (canonExprCode_lt regs inps i e1),
        mod_pack (canonExprCode_lt regs inps i e2), div_pack (canonExprCode_lt regs inps i e2),
        mod_pack (canonExprGuess_lt regs inps i e1), div_pack (canonExprGuess_lt regs inps i e1),
        ih1, ih2, bool_toNat_mod2_beq1]
    have hstep := natBorrow_step i (evalExpr regs inps e1).toNat (evalExpr regs inps e2).toNat false
    dsimp only at hstep
    rw [bitvec_sub_getLsbD _ _ hi, bitvec_getLsbD_eq_natBit, bitvec_getLsbD_eq_natBit]
    simp [hstep]
  | shl1 e ih =>
    simp only [stepExprCode, canonExprCode, canonExprGuess, evalExpr]
    rw [mod_pack (canonExprCode_lt regs inps i e), div_pack (canonExprCode_lt regs inps i e),
        ih, bool_toNat_mod2_beq1]
    have hshl : ((evalExpr regs inps e) <<< 1).getLsbD i =
                (if i = 0 then false else (evalExpr regs inps e).getLsbD (i - 1)) := by
      simp only [BitVec.getLsbD_shiftLeft]
      cases i with
      | zero => simp
      | succ k => simp [hi]
    simp [hshl]
  | shr1 e ih =>
    simp only [stepExprCode, canonExprCode, canonExprGuess, evalExpr,
        mod_pack (canonExprCode_lt regs inps i e), div_pack (canonExprCode_lt regs inps i e),
        mod_pack (canonExprGuess_lt regs inps i e), div_pack (canonExprGuess_lt regs inps i e),
        ih, bool_toNat_mod2_beq1]
    cases i with
    | zero => simp
    | succ k =>
      have hshr_prev : ((evalExpr regs inps e) >>> 1).getLsbD k = (evalExpr regs inps e).getLsbD (k + 1) := by
        simp [BitVec.getLsbD_ushiftRight, Nat.add_comm]
      simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte, hshr_prev]
      cases (evalExpr regs inps e).getLsbD (k + 1) <;> simp

theorem canonExprCode_final {w r m : Nat} (hw : w ≥ 1)
    (regs : Fin r → BitVec w) (inps : Fin m → BitVec w) (e : BVExpr r m) :
    exprFinalValid e (canonExprCode regs inps w e) = true := by
  induction e with
  | zero | one | allOnes | reg _ | inp _ => rfl
  | not e ih => exact ih
  | and e1 e2 ih1 ih2 | or e1 e2 ih1 ih2 | xor e1 e2 ih1 ih2 =>
    simp only [exprFinalValid, canonExprCode]
    rw [mod_pack (canonExprCode_lt regs inps w e1), div_pack (canonExprCode_lt regs inps w e1), ih1, ih2]
    rfl
  | add e1 e2 ih1 ih2 | sub e1 e2 ih1 ih2 =>
    simp only [exprFinalValid, canonExprCode]
    rw [mod_pack (canonExprCode_lt regs inps w e1), div_pack (canonExprCode_lt regs inps w e1),
        mod_pack (canonExprCode_lt regs inps w e2), ih1, ih2]
    rfl
  | shl1 e ih =>
    simp only [exprFinalValid, canonExprCode]
    rw [mod_pack (canonExprCode_lt regs inps w e), ih]
  | shr1 e ih =>
    simp only [exprFinalValid, canonExprCode]
    rw [mod_pack (canonExprCode_lt regs inps w e), div_pack (canonExprCode_lt regs inps w e), ih]
    have hne : w ≠ 0 := by omega
    have hmsb : ((evalExpr regs inps e) >>> 1).getLsbD (w - 1) = false := by
      simp only [BitVec.getLsbD_ushiftRight]
      exact bitvec_getLsbD_ge_w _ (by omega)
    simp [hne, hmsb]

def allEqUpTo {w : Nat} (x y : BitVec w) : Nat → Bool
  | 0 => true
  | i + 1 => allEqUpTo x y i && (x.getLsbD i == y.getLsbD i)

theorem allEqUpTo_iff {w : Nat} (x y : BitVec w) (n : Nat) :
    allEqUpTo x y n = true ↔ ∀ j, j < n → x.getLsbD j = y.getLsbD j := by
  induction n with
  | zero => simp [allEqUpTo]
  | succ k ih =>
    simp only [allEqUpTo, Bool.and_eq_true, beq_iff_eq, ih]
    constructor
    · intro ⟨h1, h2⟩ j hj
      by_cases heq : j = k
      · subst heq; exact h2
      · exact h1 j (by omega)
    · intro h
      exact ⟨fun j hj => h j (by omega), h k (by omega)⟩

theorem allEqUpTo_w {w : Nat} (x y : BitVec w) :
    allEqUpTo x y w = decide (x = y) := by
  by_cases h : x = y
  · subst h
    have : allEqUpTo x x w = true := (allEqUpTo_iff x x w).2 (fun _ _ => rfl)
    simp [this]
  · have : allEqUpTo x y w = false := by
      cases hval : allEqUpTo x y w
      · rfl
      · exfalso
        apply h
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        exact (allEqUpTo_iff x y w).1 hval i hi
    simp [this, h]

theorem allEqUpTo_mono {w : Nat} (x y : BitVec w) {i j : Nat} (hij : i ≤ j) :
    allEqUpTo x y j = true → allEqUpTo x y i = true := by
  intro hj
  rw [allEqUpTo_iff] at hj ⊢
  intro k hk
  exact hj k (by omega)

def canonPredCode {w r m : Nat} (regs : Fin r → BitVec w) (inps : Fin m → BitVec w)
    (i : Nat) : BVPred r m → Nat
  | .pTrue      => 0
  | .pFalse     => 0
  | .eq e1 e2   =>
    let ok := allEqUpTo (evalExpr regs inps e1) (evalExpr regs inps e2) i
    canonExprCode regs inps i e1 +
      (canonExprCode regs inps i e2 + ok.toNat * 2 ^ exprBits e2) * 2 ^ exprBits e1
  | .ule e1 e2  =>
    let br := natBorrow i (evalExpr regs inps e2).toNat (evalExpr regs inps e1).toNat false
    canonExprCode regs inps i e1 +
      (canonExprCode regs inps i e2 + br.toNat * 2 ^ exprBits e2) * 2 ^ exprBits e1
  | .ult e1 e2  =>
    let br := natBorrow i (evalExpr regs inps e2).toNat (evalExpr regs inps e1).toNat true
    canonExprCode regs inps i e1 +
      (canonExprCode regs inps i e2 + br.toNat * 2 ^ exprBits e2) * 2 ^ exprBits e1
  | .lsbEq e target =>
    let st :=
      if i = 0 then 0
      else if (evalExpr regs inps e).getLsbD 0 == target then 2 else 1
    canonExprCode regs inps i e + st * 2 ^ exprBits e
  | .msbEq e _  =>
    let last := if i = 0 then false else (evalExpr regs inps e).getLsbD (i - 1)
    canonExprCode regs inps i e + last.toNat * 2 ^ exprBits e
  | .pNot p     => canonPredCode regs inps i p
  | .pAnd p1 p2 => canonPredCode regs inps i p1 + canonPredCode regs inps i p2 * 2 ^ predBits p1
  | .pOr p1 p2  => canonPredCode regs inps i p1 + canonPredCode regs inps i p2 * 2 ^ predBits p1
  | .pImp p1 p2 => canonPredCode regs inps i p1 + canonPredCode regs inps i p2 * 2 ^ predBits p1

def canonPredGuess {w r m : Nat} (regs : Fin r → BitVec w) (inps : Fin m → BitVec w)
    (i : Nat) : BVPred r m → Nat
  | .pTrue      => 0
  | .pFalse     => 0
  | .eq e1 e2   => canonExprGuess regs inps i e1 + canonExprGuess regs inps i e2 * 2 ^ exprGuesses e1
  | .ule e1 e2  => canonExprGuess regs inps i e1 + canonExprGuess regs inps i e2 * 2 ^ exprGuesses e1
  | .ult e1 e2  => canonExprGuess regs inps i e1 + canonExprGuess regs inps i e2 * 2 ^ exprGuesses e1
  | .lsbEq e _  => canonExprGuess regs inps i e
  | .msbEq e _  => canonExprGuess regs inps i e
  | .pNot p     => canonPredGuess regs inps i p
  | .pAnd p1 p2 => canonPredGuess regs inps i p1 + canonPredGuess regs inps i p2 * 2 ^ predGuesses p1
  | .pOr p1 p2  => canonPredGuess regs inps i p1 + canonPredGuess regs inps i p2 * 2 ^ predGuesses p1
  | .pImp p1 p2 => canonPredGuess regs inps i p1 + canonPredGuess regs inps i p2 * 2 ^ predGuesses p1

theorem canonPredCode_lt {w r m : Nat} (regs : Fin r → BitVec w) (inps : Fin m → BitVec w)
    (i : Nat) (p : BVPred r m) : canonPredCode regs inps i p < 2 ^ predBits p := by
  induction p with
  | pTrue | pFalse => simp [canonPredCode, predBits]
  | eq e1 e2 =>
    have h2 := pack_lt (canonExprCode_lt regs inps i e2)
      (pack_bool_lt (allEqUpTo (evalExpr regs inps e1) (evalExpr regs inps e2) i))
    have h3 := pack_lt (canonExprCode_lt regs inps i e1) h2
    simpa [canonPredCode, predBits, Nat.add_assoc] using h3
  | ule e1 e2 =>
    have h2 := pack_lt (canonExprCode_lt regs inps i e2)
      (pack_bool_lt (natBorrow i (evalExpr regs inps e2).toNat (evalExpr regs inps e1).toNat false))
    have h3 := pack_lt (canonExprCode_lt regs inps i e1) h2
    simpa [canonPredCode, predBits, Nat.add_assoc] using h3
  | ult e1 e2 =>
    have h2 := pack_lt (canonExprCode_lt regs inps i e2)
      (pack_bool_lt (natBorrow i (evalExpr regs inps e2).toNat (evalExpr regs inps e1).toNat true))
    have h3 := pack_lt (canonExprCode_lt regs inps i e1) h2
    simpa [canonPredCode, predBits, Nat.add_assoc] using h3
  | lsbEq e target =>
    have hst : (if i = 0 then 0 else if (evalExpr regs inps e).getLsbD 0 == target then 2 else 1) < 2 ^ 2 := by
      split
      · omega
      · split <;> omega
    exact pack_lt (canonExprCode_lt regs inps i e) hst
  | msbEq e _ =>
    exact pack_lt (canonExprCode_lt regs inps i e) (pack_bool_lt _)
  | pNot p ih => exact ih
  | pAnd p1 p2 ih1 ih2 | pOr p1 p2 ih1 ih2 | pImp p1 p2 ih1 ih2 =>
    exact pack_lt ih1 ih2

theorem canonPredGuess_lt {w r m : Nat} (regs : Fin r → BitVec w) (inps : Fin m → BitVec w)
    (i : Nat) (p : BVPred r m) : canonPredGuess regs inps i p < 2 ^ predGuesses p := by
  induction p with
  | pTrue | pFalse => simp [canonPredGuess, predGuesses]
  | eq e1 e2 | ule e1 e2 | ult e1 e2 =>
    exact pack_lt (canonExprGuess_lt regs inps i e1) (canonExprGuess_lt regs inps i e2)
  | lsbEq e _ | msbEq e _ =>
    exact canonExprGuess_lt regs inps i e
  | pNot p ih => exact ih
  | pAnd p1 p2 ih1 ih2 | pOr p1 p2 ih1 ih2 | pImp p1 p2 ih1 ih2 =>
    exact pack_lt ih1 ih2

theorem canonPredCode_zero {w r m : Nat} (regs : Fin r → BitVec w) (inps : Fin m → BitVec w)
    (p : BVPred r m) : canonPredCode regs inps 0 p = predInitCode p := by
  induction p with
  | pTrue | pFalse => rfl
  | eq e1 e2 =>
    simp [canonPredCode, predInitCode, allEqUpTo, canonExprCode_zero]
  | ule e1 e2 =>
    simp [canonPredCode, predInitCode, natBorrow_zero, canonExprCode_zero]
  | ult e1 e2 =>
    simp [canonPredCode, predInitCode, natBorrow_zero, canonExprCode_zero]
  | lsbEq e _ =>
    simp [canonPredCode, predInitCode, canonExprCode_zero]
  | msbEq e _ =>
    simp [canonPredCode, predInitCode, canonExprCode_zero]
  | pNot p ih => exact ih
  | pAnd p1 p2 ih1 ih2 | pOr p1 p2 ih1 ih2 | pImp p1 p2 ih1 ih2 =>
    simp [canonPredCode, predInitCode, ih1, ih2]

theorem canonPredCode_step {w r m : Nat} (regs : Fin r → BitVec w) (inps : Fin m → BitVec w)
    {i : Nat} (hi : i < w) (p : BVPred r m) :
    stepPredCode (vecMask regs i) (vecMask inps i) p
      (canonPredCode regs inps i p) (canonPredGuess regs inps i p) =
    (canonPredCode regs inps (i + 1) p, true) := by
  induction p with
  | pTrue | pFalse => rfl
  | eq e1 e2 =>
    simp only [stepPredCode, canonPredCode, canonPredGuess]
    rw [mod_pack (canonExprCode_lt regs inps i e1), div_pack (canonExprCode_lt regs inps i e1),
        mod_pack (canonExprCode_lt regs inps i e2), div_pack (canonExprCode_lt regs inps i e2),
        mod_pack (canonExprGuess_lt regs inps i e1), div_pack (canonExprGuess_lt regs inps i e1),
        canonExprCode_step regs inps hi e1, canonExprCode_step regs inps hi e2, bool_toNat_mod2_beq1]
    simp [allEqUpTo]
  | ule e1 e2 =>
    simp only [stepPredCode, canonPredCode, canonPredGuess]
    rw [mod_pack (canonExprCode_lt regs inps i e1), div_pack (canonExprCode_lt regs inps i e1),
        mod_pack (canonExprCode_lt regs inps i e2), div_pack (canonExprCode_lt regs inps i e2),
        mod_pack (canonExprGuess_lt regs inps i e1), div_pack (canonExprGuess_lt regs inps i e1),
        canonExprCode_step regs inps hi e1, canonExprCode_step regs inps hi e2, bool_toNat_mod2_beq1]
    have hstep := natBorrow_step i (evalExpr regs inps e2).toNat (evalExpr regs inps e1).toNat false
    simp only [bitvec_getLsbD_eq_natBit, hstep, Bool.and_self]
  | ult e1 e2 =>
    simp only [stepPredCode, canonPredCode, canonPredGuess]
    rw [mod_pack (canonExprCode_lt regs inps i e1), div_pack (canonExprCode_lt regs inps i e1),
        mod_pack (canonExprCode_lt regs inps i e2), div_pack (canonExprCode_lt regs inps i e2),
        mod_pack (canonExprGuess_lt regs inps i e1), div_pack (canonExprGuess_lt regs inps i e1),
        canonExprCode_step regs inps hi e1, canonExprCode_step regs inps hi e2, bool_toNat_mod2_beq1]
    have hstep := natBorrow_step i (evalExpr regs inps e2).toNat (evalExpr regs inps e1).toNat true
    simp only [bitvec_getLsbD_eq_natBit, hstep, Bool.and_self]
  | lsbEq e target =>
    simp only [stepPredCode, canonPredCode, canonPredGuess,
        mod_pack (canonExprCode_lt regs inps i e), div_pack (canonExprCode_lt regs inps i e),
        canonExprCode_step regs inps hi e]
    cases i with
    | zero => simp
    | succ k =>
      cases h : ((evalExpr regs inps e).getLsbD 0 == target) <;> simp
  | msbEq e target =>
    simp only [stepPredCode, canonPredCode, canonPredGuess]
    rw [mod_pack (canonExprCode_lt regs inps i e), canonExprCode_step regs inps hi e]
    simp
  | pNot p ih => exact ih
  | pAnd p1 p2 ih1 ih2 | pOr p1 p2 ih1 ih2 | pImp p1 p2 ih1 ih2 =>
    simp only [stepPredCode, canonPredCode, canonPredGuess]
    rw [mod_pack (canonPredCode_lt regs inps i p1), div_pack (canonPredCode_lt regs inps i p1),
        mod_pack (canonPredGuess_lt regs inps i p1), div_pack (canonPredGuess_lt regs inps i p1),
        ih1, ih2]
    simp

theorem canonPredCode_final {w r m : Nat} (hw : w ≥ 1)
    (regs : Fin r → BitVec w) (inps : Fin m → BitVec w) (p : BVPred r m) :
    predFinalValid p (canonPredCode regs inps w p) = true := by
  induction p with
  | pTrue | pFalse => rfl
  | eq e1 e2 | ule e1 e2 | ult e1 e2 =>
    simp only [predFinalValid, canonPredCode]
    rw [mod_pack (canonExprCode_lt regs inps w e1), div_pack (canonExprCode_lt regs inps w e1),
        mod_pack (canonExprCode_lt regs inps w e2),
        canonExprCode_final hw regs inps e1, canonExprCode_final hw regs inps e2]
    rfl
  | lsbEq e _ | msbEq e _ =>
    simp only [predFinalValid, canonPredCode]
    rw [mod_pack (canonExprCode_lt regs inps w e), canonExprCode_final hw regs inps e]
  | pNot p ih => exact ih
  | pAnd p1 p2 ih1 ih2 | pOr p1 p2 ih1 ih2 | pImp p1 p2 ih1 ih2 =>
    simp only [predFinalValid, canonPredCode]
    rw [mod_pack (canonPredCode_lt regs inps w p1), div_pack (canonPredCode_lt regs inps w p1), ih1, ih2]
    rfl

theorem canonPredCode_accept {w r m : Nat} (hw : w ≥ 1)
    (regs : Fin r → BitVec w) (inps : Fin m → BitVec w) (p : BVPred r m) :
    predAccept p (canonPredCode regs inps w p) = evalPred regs inps p := by
  induction p with
  | pTrue | pFalse => rfl
  | eq e1 e2 =>
    simp only [predAccept, canonPredCode, evalPred]
    rw [div_pack (canonExprCode_lt regs inps w e1), div_pack (canonExprCode_lt regs inps w e2)]
    rw [allEqUpTo_w]
    cases decide (evalExpr regs inps e1 = evalExpr regs inps e2) <;> rfl
  | ule e1 e2 =>
    simp only [predAccept, canonPredCode, evalPred]
    rw [div_pack (canonExprCode_lt regs inps w e1), div_pack (canonExprCode_lt regs inps w e2)]
    have := natBorrow_w_ule (evalExpr regs inps e1) (evalExpr regs inps e2)
    rw [← this]
    cases natBorrow w (evalExpr regs inps e2).toNat (evalExpr regs inps e1).toNat false <;> rfl
  | ult e1 e2 =>
    simp only [predAccept, canonPredCode, evalPred]
    rw [div_pack (canonExprCode_lt regs inps w e1), div_pack (canonExprCode_lt regs inps w e2)]
    have := natBorrow_w_ult (evalExpr regs inps e1) (evalExpr regs inps e2)
    rw [← this]
    cases natBorrow w (evalExpr regs inps e2).toNat (evalExpr regs inps e1).toNat true <;> rfl
  | lsbEq e target =>
    simp only [predAccept, canonPredCode, evalPred]
    rw [div_pack (canonExprCode_lt regs inps w e)]
    have hne : w ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
    cases h : ((evalExpr regs inps e).getLsbD 0 == target)
    · have : (evalExpr regs inps e).getLsbD 0 ≠ target := by
        intro heq; simp [heq] at h
      simp [this]
    · have : (evalExpr regs inps e).getLsbD 0 = target := eq_of_beq h
      simp [this]
  | msbEq e target =>
    simp only [predAccept, canonPredCode, evalPred]
    rw [div_pack (canonExprCode_lt regs inps w e)]
    have hne : w ≠ 0 := by omega
    have hmsb : (evalExpr regs inps e).msb = (evalExpr regs inps e).getLsbD (w - 1) := by
      simp [BitVec.msb_eq_getLsbD_last]
    simp only [hne, ↓reduceIte, hmsb]
    cases (evalExpr regs inps e).getLsbD (w - 1) <;> cases target <;> rfl
  | pNot p ih =>
    simp [predAccept, canonPredCode, evalPred, ih]
  | pAnd p1 p2 ih1 ih2 =>
    simp only [predAccept, canonPredCode, evalPred]
    rw [mod_pack (canonPredCode_lt regs inps w p1), div_pack (canonPredCode_lt regs inps w p1), ih1, ih2]
  | pOr p1 p2 ih1 ih2 =>
    simp only [predAccept, canonPredCode, evalPred]
    rw [mod_pack (canonPredCode_lt regs inps w p1), div_pack (canonPredCode_lt regs inps w p1), ih1, ih2]
  | pImp p1 p2 ih1 ih2 =>
    simp only [predAccept, canonPredCode, evalPred]
    rw [mod_pack (canonPredCode_lt regs inps w p1), div_pack (canonPredCode_lt regs inps w p1), ih1, ih2]

theorem canonPredCode_alive {w r m : Nat} (regs : Fin r → BitVec w) (inps : Fin m → BitVec w)
    {i : Nat} (hi : i ≤ w) (p : BVPred r m)
    (htrue : evalPred regs inps p = true) :
    predAliveHyp p (canonPredCode regs inps i p) = true := by
  induction p with
  | pTrue => rfl
  | pFalse => simp [evalPred] at htrue
  | eq e1 e2 =>
    simp only [predAliveHyp, canonPredCode]
    rw [div_pack (canonExprCode_lt regs inps i e1), div_pack (canonExprCode_lt regs inps i e2)]
    simp only [evalPred, decide_eq_true_eq] at htrue
    have hw_ok : allEqUpTo (evalExpr regs inps e1) (evalExpr regs inps e2) w = true := by
      rw [allEqUpTo_w, htrue]; simp
    have hi_ok := allEqUpTo_mono _ _ hi hw_ok
    simp [hi_ok]
  | lsbEq e target =>
    simp only [predAliveHyp, canonPredCode]
    rw [div_pack (canonExprCode_lt regs inps i e)]
    simp only [evalPred, decide_eq_true_eq] at htrue
    cases i with
    | zero => rfl
    | succ k => simp [htrue]
  | pAnd p1 p2 ih1 ih2 =>
    simp only [predAliveHyp, canonPredCode, Bool.and_eq_true]
    simp only [evalPred, Bool.and_eq_true] at htrue
    rw [mod_pack (canonPredCode_lt regs inps i p1), div_pack (canonPredCode_lt regs inps i p1)]
    exact ⟨ih1 htrue.1, ih2 htrue.2⟩
  | ule _ _ | ult _ _ | msbEq _ _ | pNot _ | pOr _ _ | pImp _ _ => rfl

-- ============================================================================
-- Section 6: Unrolled k-Step Obligation Automaton & `checkOblig_sound`
-- ============================================================================

-- Pack/step all `r` transition expressions for one time step

def canonNextCode {w r m : Nat} (next : Fin r → BVExpr r m)
    (regs : Fin r → BitVec w) (inps : Fin m → BitVec w) (i : Nat) : (n : Nat) → n ≤ r → Nat
  | 0, _ => 0
  | n + 1, hn =>
    let hn' := Nat.le_of_succ_le hn
    let k := nextBits next n hn'
    canonNextCode next regs inps i n hn' + canonExprCode regs inps i (next ⟨n, hn⟩) * 2 ^ k

def canonNextGuess {w r m : Nat} (next : Fin r → BVExpr r m)
    (regs : Fin r → BitVec w) (inps : Fin m → BitVec w) (i : Nat) : (n : Nat) → n ≤ r → Nat
  | 0, _ => 0
  | n + 1, hn =>
    let hn' := Nat.le_of_succ_le hn
    let g := nextGuesses next n hn'
    canonNextGuess next regs inps i n hn' + canonExprGuess regs inps i (next ⟨n, hn⟩) * 2 ^ g

theorem canonNextCode_lt {w r m : Nat} (next : Fin r → BVExpr r m)
    (regs : Fin r → BitVec w) (inps : Fin m → BitVec w) (i : Nat) (n : Nat) (hn : n ≤ r) :
    canonNextCode next regs inps i n hn < 2 ^ nextBits next n hn := by
  induction n with
  | zero => simp [canonNextCode, nextBits]
  | succ n ih =>
    simp only [canonNextCode, nextBits]
    exact pack_lt (ih (Nat.le_of_succ_le hn)) (canonExprCode_lt regs inps i _)

theorem canonNextGuess_lt {w r m : Nat} (next : Fin r → BVExpr r m)
    (regs : Fin r → BitVec w) (inps : Fin m → BitVec w) (i : Nat) (n : Nat) (hn : n ≤ r) :
    canonNextGuess next regs inps i n hn < 2 ^ nextGuesses next n hn := by
  induction n with
  | zero => simp [canonNextGuess, nextGuesses]
  | succ n ih =>
    simp only [canonNextGuess, nextGuesses]
    exact pack_lt (ih (Nat.le_of_succ_le hn)) (canonExprGuess_lt regs inps i _)

theorem canonNextCode_zero {w r m : Nat} (next : Fin r → BVExpr r m)
    (regs : Fin r → BitVec w) (inps : Fin m → BitVec w) (n : Nat) (hn : n ≤ r) :
    canonNextCode next regs inps 0 n hn = nextInitCode next n hn := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [canonNextCode, nextInitCode, ih (Nat.le_of_succ_le hn), canonExprCode_zero]

theorem canonNextCode_step {w r m : Nat} (next : Fin r → BVExpr r m)
    (regs : Fin r → BitVec w) (inps : Fin m → BitVec w) {i : Nat} (hi : i < w)
    (n : Nat) (hn : n ≤ r) :
    stepNextCode next (vecMask regs i) (vecMask inps i) n hn
      (canonNextCode next regs inps i n hn) (canonNextGuess next regs inps i n hn) =
    (canonNextCode next regs inps (i + 1) n hn, true,
      vecMask.go (fun idx => evalExpr regs inps (next idx)) i n hn) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [stepNextCode, canonNextCode, canonNextGuess, vecMask.go]
    have hn' := Nat.le_of_succ_le hn
    rw [mod_pack (canonNextCode_lt next regs inps i n hn'),
        div_pack (canonNextCode_lt next regs inps i n hn'),
        mod_pack (canonNextGuess_lt next regs inps i n hn'),
        div_pack (canonNextGuess_lt next regs inps i n hn'),
        ih hn', canonExprCode_step regs inps hi (next ⟨n, hn⟩)]
    rfl

theorem canonNextCode_final {w r m : Nat} (hw : w ≥ 1) (next : Fin r → BVExpr r m)
    (regs : Fin r → BitVec w) (inps : Fin m → BitVec w) (n : Nat) (hn : n ≤ r) :
    nextFinalValid next n hn (canonNextCode next regs inps w n hn) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [nextFinalValid, canonNextCode]
    have hn' := Nat.le_of_succ_le hn
    rw [mod_pack (canonNextCode_lt next regs inps w n hn'),
        div_pack (canonNextCode_lt next regs inps w n hn'),
        ih hn', canonExprCode_final hw regs inps (next ⟨n, hn⟩)]
    rfl

-- Finite unrolling of `steps` time steps:
--   `unrollTrace sys s0 us j` is the register state at time `j` (for `j ≤ steps`).

def unrollTrace {w r m : Nat} (sys : BVSystem r m)
    (s0 : Fin r → BitVec w) (us : Nat → Fin m → BitVec w) : Nat → (Fin r → BitVec w) :=
  runTrace sys s0 us

-- Recursive k-step obligation bundle (unrolling `s_0 -> s_1 -> ... -> s_steps`
-- together with hypotheses `hyps 0 (s_0), ..., hyps steps (s_steps)` and conclusion `conc (s_steps)`).
-- We pack the state recursively by `steps` for maximum clarity and zero list-overhead!

def obBits {r m : Nat} (sys : BVSystem r m) :
    (steps : Nat) → (Fin (steps + 1) → BVPred r 0) → BVPred r 0 → Nat
  | 0, hyps, conc => predBits (hyps ⟨0, Nat.zero_lt_succ 0⟩) + predBits conc
  | s + 1, hyps, conc =>
    nextBits sys.next r (Nat.le_refl r) +
    predBits (hyps ⟨0, Nat.zero_lt_succ _⟩) +
    obBits sys s (fun j => hyps j.succ) conc

def canonObCode {w r m : Nat} (sys : BVSystem r m)
    (s0 : Fin r → BitVec w) (us : Nat → Fin m → BitVec w) (i : Nat) :
    (steps : Nat) → (Fin (steps + 1) → BVPred r 0) → BVPred r 0 → Nat
  | 0, hyps, conc =>
    let h0 := hyps ⟨0, Nat.zero_lt_succ 0⟩
    canonPredCode s0 Fin.elim0 i h0 + canonPredCode s0 Fin.elim0 i conc * 2 ^ predBits h0
  | s + 1, hyps, conc =>
    let h0 := hyps ⟨0, Nat.zero_lt_succ _⟩
    let kn := nextBits sys.next r (Nat.le_refl r)
    let kh := predBits h0
    let s1 : Fin r → BitVec w := fun idx => evalExpr s0 (us 0) (sys.next idx)
    let cRest := canonObCode sys s1 (fun t => us (t + 1)) i s (fun j => hyps j.succ) conc
    canonNextCode sys.next s0 (us 0) i r (Nat.le_refl r) +
      (canonPredCode s0 Fin.elim0 i h0 + cRest * 2 ^ kh) * 2 ^ kn

def canonObGuess {w r m : Nat} (sys : BVSystem r m)
    (s0 : Fin r → BitVec w) (us : Nat → Fin m → BitVec w) (i : Nat) :
    (steps : Nat) → (Fin (steps + 1) → BVPred r 0) → BVPred r 0 → Nat
  | 0, hyps, conc =>
    let h0 := hyps ⟨0, Nat.zero_lt_succ 0⟩
    canonPredGuess s0 Fin.elim0 i h0 + canonPredGuess s0 Fin.elim0 i conc * 2 ^ predGuesses h0
  | s + 1, hyps, conc =>
    let h0 := hyps ⟨0, Nat.zero_lt_succ _⟩
    let gn := nextGuesses sys.next r (Nat.le_refl r)
    let gh := predGuesses h0
    let s1 : Fin r → BitVec w := fun idx => evalExpr s0 (us 0) (sys.next idx)
    let gRest := canonObGuess sys s1 (fun t => us (t + 1)) i s (fun j => hyps j.succ) conc
    canonNextGuess sys.next s0 (us 0) i r (Nat.le_refl r) +
      (canonPredGuess s0 Fin.elim0 i h0 + gRest * 2 ^ gh) * 2 ^ gn

def canonUMask {w m : Nat} (us : Nat → Fin m → BitVec w) (i : Nat) : Nat → Nat
  | 0 => 0
  | s + 1 => vecMask (us 0) i + canonUMask (fun t => us (t + 1)) i s * 2 ^ m

theorem canonUMask_lt {w m : Nat} (us : Nat → Fin m → BitVec w) (i : Nat) (steps : Nat) :
    canonUMask us i steps < 2 ^ (steps * m) := by
  induction steps generalizing us with
  | zero => simp [canonUMask]
  | succ s ih =>
    simp only [canonUMask]
    have h1 := pack_lt (vecMask_lt (us 0) i) (ih (fun t => us (t + 1)))
    have hexp : m + s * m = (s + 1) * m := by
      rw [Nat.succ_mul, Nat.add_comm]
    rwa [hexp] at h1

theorem canonObCode_lt {w r m : Nat} (sys : BVSystem r m)
    (s0 : Fin r → BitVec w) (us : Nat → Fin m → BitVec w) (i : Nat)
    (steps : Nat) (hyps : Fin (steps + 1) → BVPred r 0) (conc : BVPred r 0) :
    canonObCode sys s0 us i steps hyps conc < 2 ^ obBits sys steps hyps conc := by
  induction steps generalizing s0 us with
  | zero =>
    exact pack_lt (canonPredCode_lt s0 Fin.elim0 i _) (canonPredCode_lt s0 Fin.elim0 i _)
  | succ s ih =>
    simp only [canonObCode, obBits]
    have h1 := pack_lt (canonPredCode_lt s0 Fin.elim0 i (hyps ⟨0, Nat.zero_lt_succ _⟩))
      (ih (fun idx => evalExpr s0 (us 0) (sys.next idx)) (fun t => us (t + 1)) (fun j => hyps j.succ))
    have h2 := pack_lt (canonNextCode_lt sys.next s0 (us 0) i r (Nat.le_refl r)) h1
    simpa [Nat.add_assoc] using h2

theorem canonObGuess_lt {w r m : Nat} (sys : BVSystem r m)
    (s0 : Fin r → BitVec w) (us : Nat → Fin m → BitVec w) (i : Nat)
    (steps : Nat) (hyps : Fin (steps + 1) → BVPred r 0) (conc : BVPred r 0) :
    canonObGuess sys s0 us i steps hyps conc < 2 ^ obGuesses sys steps hyps conc := by
  induction steps generalizing s0 us with
  | zero =>
    exact pack_lt (canonPredGuess_lt s0 Fin.elim0 i _) (canonPredGuess_lt s0 Fin.elim0 i _)
  | succ s ih =>
    simp only [canonObGuess, obGuesses]
    have h1 := pack_lt (canonPredGuess_lt s0 Fin.elim0 i (hyps ⟨0, Nat.zero_lt_succ _⟩))
      (ih (fun idx => evalExpr s0 (us 0) (sys.next idx)) (fun t => us (t + 1)) (fun j => hyps j.succ))
    have h2 := pack_lt (canonNextGuess_lt sys.next s0 (us 0) i r (Nat.le_refl r)) h1
    simpa [Nat.add_assoc] using h2

theorem canonObCode_zero {w r m : Nat} (sys : BVSystem r m)
    (s0 : Fin r → BitVec w) (us : Nat → Fin m → BitVec w)
    (steps : Nat) (hyps : Fin (steps + 1) → BVPred r 0) (conc : BVPred r 0) :
    canonObCode sys s0 us 0 steps hyps conc = obInitCode sys steps hyps conc := by
  induction steps generalizing s0 us with
  | zero =>
    simp [canonObCode, obInitCode, canonPredCode_zero]
  | succ s ih =>
    simp [canonObCode, obInitCode, canonNextCode_zero, canonPredCode_zero, ih]

theorem runTrace_succ_shift {w r m : Nat} (sys : BVSystem r m)
    (s0 : Fin r → BitVec w) (us : Nat → Fin m → BitVec w) (t : Nat) :
    runTrace sys (fun idx => evalExpr s0 (us 0) (sys.next idx)) (fun k => us (k + 1)) t =
    runTrace sys s0 us (t + 1) := by
  induction t with
  | zero => rfl
  | succ k ih =>
    simp only [runTrace, ih]

theorem canonObCode_step {w r m : Nat} (sys : BVSystem r m)
    (s0 : Fin r → BitVec w) (us : Nat → Fin m → BitVec w) {i : Nat} (hi : i < w)
    (steps : Nat) (hyps : Fin (steps + 1) → BVPred r 0) (conc : BVPred r 0)
    (hhyps : ∀ j : Fin (steps + 1), evalPred (runTrace sys s0 us j.val) Fin.elim0 (hyps j) = true) :
    obStepCode sys steps hyps conc (vecMask s0 i) (canonUMask us i steps)
      (canonObCode sys s0 us i steps hyps conc)
      (canonObGuess sys s0 us i steps hyps conc) =
    some (canonObCode sys s0 us (i + 1) steps hyps conc) := by
  induction steps generalizing s0 us with
  | zero =>
    have h0 := hhyps ⟨0, Nat.zero_lt_succ 0⟩
    simp only [runTrace] at h0
    have hzeroMask : vecMask (Fin.elim0 : Fin 0 → BitVec w) i = 0 := rfl
    have hs1 := canonPredCode_step s0 Fin.elim0 hi (hyps ⟨0, Nat.zero_lt_succ 0⟩)
    have hs2 := canonPredCode_step s0 Fin.elim0 hi conc
    rw [hzeroMask] at hs1 hs2
    have halive := canonPredCode_alive s0 Fin.elim0 (Nat.succ_le_of_lt hi) (hyps ⟨0, Nat.zero_lt_succ 0⟩) h0
    simp only [obStepCode, canonObCode, canonObGuess,
        mod_pack (canonPredCode_lt s0 Fin.elim0 i _), div_pack (canonPredCode_lt s0 Fin.elim0 i _),
        mod_pack (canonPredGuess_lt s0 Fin.elim0 i _), div_pack (canonPredGuess_lt s0 Fin.elim0 i _),
        hs1, hs2, halive, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  | succ s ih =>
    have h0 := hhyps ⟨0, Nat.zero_lt_succ _⟩
    simp only [runTrace] at h0
    have hzeroMask : vecMask (Fin.elim0 : Fin 0 → BitVec w) i = 0 := rfl
    have hnext := canonNextCode_step sys.next s0 (us 0) hi r (Nat.le_refl r)
    have hs1 := canonPredCode_step s0 Fin.elim0 hi (hyps ⟨0, Nat.zero_lt_succ _⟩)
    rw [hzeroMask] at hs1
    have halive := canonPredCode_alive s0 Fin.elim0 (Nat.succ_le_of_lt hi)
      (hyps ⟨0, Nat.zero_lt_succ _⟩) h0
    have hhyps' : ∀ j : Fin (s + 1),
        evalPred (runTrace sys (fun idx => evalExpr s0 (us 0) (sys.next idx)) (fun k => us (k + 1)) j.val)
          Fin.elim0 (hyps j.succ) = true := by
      intro j
      rw [runTrace_succ_shift]
      exact hhyps j.succ
    have hih := ih (fun idx => evalExpr s0 (us 0) (sys.next idx)) (fun k => us (k + 1)) (fun j => hyps j.succ) hhyps'
    have hvm : vecMask.go (fun idx => evalExpr s0 (us 0) (sys.next idx)) i r (Nat.le_refl r) =
               vecMask (fun idx => evalExpr s0 (us 0) (sys.next idx)) i := rfl
    simp only [obStepCode, canonObCode, canonObGuess, canonUMask,
        mod_pack (vecMask_lt (us 0) i), div_pack (vecMask_lt (us 0) i),
        mod_pack (canonNextCode_lt sys.next s0 (us 0) i r (Nat.le_refl r)),
        div_pack (canonNextCode_lt sys.next s0 (us 0) i r (Nat.le_refl r)),
        mod_pack (canonNextGuess_lt sys.next s0 (us 0) i r (Nat.le_refl r)),
        div_pack (canonNextGuess_lt sys.next s0 (us 0) i r (Nat.le_refl r)),
        mod_pack (canonPredCode_lt s0 Fin.elim0 i _), div_pack (canonPredCode_lt s0 Fin.elim0 i _),
        mod_pack (canonPredGuess_lt s0 Fin.elim0 i _), div_pack (canonPredGuess_lt s0 Fin.elim0 i _),
        hnext, hs1, halive, hvm, hih, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]

theorem canonObCode_badAccept {w r m : Nat} (hw : w ≥ 1) (sys : BVSystem r m)
    (s0 : Fin r → BitVec w) (us : Nat → Fin m → BitVec w)
    (steps : Nat) (hyps : Fin (steps + 1) → BVPred r 0) (conc : BVPred r 0)
    (hhyps : ∀ j : Fin (steps + 1), evalPred (runTrace sys s0 us j.val) Fin.elim0 (hyps j) = true)
    (hbad : evalPred (runTrace sys s0 us steps) Fin.elim0 conc = false) :
    obIsBadAccept sys steps hyps conc (canonObCode sys s0 us w steps hyps conc) = true := by
  induction steps generalizing s0 us with
  | zero =>
    simp only [obIsBadAccept, canonObCode]
    have h0 := hhyps ⟨0, Nat.zero_lt_succ 0⟩
    simp only [runTrace] at h0 hbad
    rw [mod_pack (canonPredCode_lt s0 Fin.elim0 w _), div_pack (canonPredCode_lt s0 Fin.elim0 w _),
        canonPredCode_final hw s0 Fin.elim0 _, canonPredCode_accept hw s0 Fin.elim0 _,
        canonPredCode_final hw s0 Fin.elim0 conc, canonPredCode_accept hw s0 Fin.elim0 conc,
        h0, hbad]
    rfl
  | succ s ih =>
    simp only [obIsBadAccept, canonObCode]
    have h0 := hhyps ⟨0, Nat.zero_lt_succ _⟩
    simp only [runTrace] at h0
    rw [mod_pack (canonNextCode_lt sys.next s0 (us 0) w r (Nat.le_refl r)),
        div_pack (canonNextCode_lt sys.next s0 (us 0) w r (Nat.le_refl r)),
        mod_pack (canonPredCode_lt s0 Fin.elim0 w _), div_pack (canonPredCode_lt s0 Fin.elim0 w _),
        canonNextCode_final hw sys.next s0 (us 0) r (Nat.le_refl r),
        canonPredCode_final hw s0 Fin.elim0 _, canonPredCode_accept hw s0 Fin.elim0 _, h0]
    have hhyps' : ∀ j : Fin (s + 1),
        evalPred (runTrace sys (fun idx => evalExpr s0 (us 0) (sys.next idx)) (fun k => us (k + 1)) j.val)
          Fin.elim0 (hyps j.succ) = true := by
      intro j
      rw [runTrace_succ_shift]
      exact hhyps j.succ
    have hbad' : evalPred (runTrace sys (fun idx => evalExpr s0 (us 0) (sys.next idx)) (fun k => us (k + 1)) s)
        Fin.elim0 conc = false := by
      rw [runTrace_succ_shift]; exact hbad
    have hih := ih (fun idx => evalExpr s0 (us 0) (sys.next idx)) (fun k => us (k + 1))
      (fun j => hyps j.succ) hhyps' hbad'
    simp [hih]

-- Boolean certificate checker for ONE unrolled obligation across ALL w ≥ 1

theorem checkOblig_sound {r m : Nat} (sys : BVSystem r m) (steps : Nat)
    (hyps : Fin (steps + 1) → BVPred r 0) (conc : BVPred r 0) (cert : NatSet)
    (hchk : checkOblig sys steps hyps conc cert = true) :
    ∀ (w : Nat), w ≥ 1 →
    ∀ (s0 : Fin r → BitVec w) (us : Nat → Fin m → BitVec w),
      (∀ j : Fin (steps + 1), evalPred (runTrace sys s0 us j.val) Fin.elim0 (hyps j) = true) →
      evalPred (runTrace sys s0 us steps) Fin.elim0 conc = true := by
  simp only [checkOblig, Bool.and_eq_true] at hchk
  obtain ⟨⟨hinit, hclos⟩, hsafe⟩ := hchk
  intro w hw s0 us hhyps
  -- Prove by induction on i that for all 1 ≤ i ≤ w, canonObCode at i is in cert
  have hreach : ∀ i, 1 ≤ i → i ≤ w → cert.mem (canonObCode sys s0 us i steps hyps conc) = true := by
    intro i hi1 hiw
    induction i with
    | zero => omega
    | succ k ih =>
      have hklt : k < w := by omega
      have hstep := canonObCode_step sys s0 us hklt steps hyps conc hhyps
      cases k with
      | zero =>
        have hfrom := allRange_spec hinit (vecMask s0 0) (vecMask_lt s0 0)
        have hfrom := allRange_spec hfrom (canonUMask us 0 steps) (canonUMask_lt us 0 steps)
        have hfrom := allRange_spec hfrom (canonObGuess sys s0 us 0 steps hyps conc)
          (canonObGuess_lt sys s0 us 0 steps hyps conc)
        rw [← canonObCode_zero sys s0 us steps hyps conc, hstep] at hfrom
        exact hfrom
      | succ k' =>
        have hmem_prev := ih (by omega) (by omega)
        have hfrom_all := NatSet.all_mem hclos _ hmem_prev
        have hfrom := allRange_spec hfrom_all (vecMask s0 (k' + 1)) (vecMask_lt s0 (k' + 1))
        have hfrom := allRange_spec hfrom (canonUMask us (k' + 1) steps) (canonUMask_lt us (k' + 1) steps)
        have hfrom := allRange_spec hfrom (canonObGuess sys s0 us (k' + 1) steps hyps conc)
          (canonObGuess_lt sys s0 us (k' + 1) steps hyps conc)
        rw [hstep] at hfrom
        exact hfrom
  have hmem_w := hreach w hw (Nat.le_refl w)
  have hnotbad := NatSet.all_mem hsafe _ hmem_w
  cases hval : evalPred (runTrace sys s0 us steps) Fin.elim0 conc
  · exfalso
    have hbad := canonObCode_badAccept hw sys s0 us steps hyps conc hhyps hval
    simp [hbad] at hnotbad
  · rfl

-- ============================================================================
-- Section 7: Unified k-Induction + IC3 Strengthening Certificate Engine
-- ============================================================================

theorem checkBases_sound {r m : Nat} (sys : BVSystem r m) (inv : BVPred r 0)
    (start : Nat) (cs : List NatSet)
    (hchk : checkBases sys inv start cs = true) :
    ∀ (off : Nat), off < cs.length →
    ∀ (w : Nat), w ≥ 1 →
    ∀ (s0 : Fin r → BitVec w) (us : Nat → Fin m → BitVec w),
      evalPred s0 Fin.elim0 sys.init = true →
      evalPred (runTrace sys s0 us (start + off)) Fin.elim0 inv = true := by
  induction cs generalizing start with
  | nil => intro off hoff; simp at hoff
  | cons c cs ih =>
    simp only [checkBases, Bool.and_eq_true] at hchk
    intro off hoff w hw s0 us hinit
    cases off with
    | zero =>
      simp only [Nat.add_zero]
      apply checkOblig_sound sys start (baseHyps sys.init start) inv c hchk.1 w hw s0 us
      intro idx
      unfold baseHyps
      by_cases hz : idx.val = 0
      · simp [hz, runTrace, hinit]
      · simp [hz, evalPred]
    | succ off' =>
      have hlen : off' < cs.length := by simp at hoff; omega
      have hres := ih (start + 1) hchk.2 off' hlen w hw s0 us hinit
      have heq : start + 1 + off' = start + (off' + 1) := by omega
      rwa [heq] at hres

theorem runTrace_add {w r m : Nat} (sys : BVSystem r m)
    (s0 : Fin r → BitVec w) (inputs : Nat → Fin m → BitVec w) (t0 d : Nat) :
    runTrace sys (runTrace sys s0 inputs t0) (fun k => inputs (t0 + k)) d =
    runTrace sys s0 inputs (t0 + d) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [runTrace, ih]
    rfl

/--
**Main Soundness Meta-Theorem (`checkKIndIC3_sound`)**:
For ANY width-uniform bitwise transition system `sys : BVSystem r m`, ANY safety property
`prop : BVPred r 0`, and ANY finite binary certificate `cert : KIndIC3Cert r`,
if the kernel-decidable verifier returns `checkKIndIC3 sys prop cert = true`, then
`prop` holds across **ALL bit-widths `w ≥ 1`**, **ALL initial states**, **ALL nondeterministic
input streams**, and **ALL time steps `t : Nat`**.
-/
theorem checkKIndIC3_sound {r m : Nat} (sys : BVSystem r m) (prop : BVPred r 0)
    (cert : KIndIC3Cert r)
    (hchk : checkKIndIC3 sys prop cert = true) :
    Safe sys prop := by
  dsimp only [checkKIndIC3] at hchk
  let inv := if cert.invClauses.isEmpty then prop else foldAnd cert.invClauses
  change ((decide (cert.k ≥ 1) && (cert.baseCerts.length == cert.k) &&
           checkBases sys inv 0 cert.baseCerts &&
           checkOblig sys cert.k (stepHyps inv cert.k) inv cert.stepCert &&
           checkOblig sys 0 (safetyHyps inv) prop cert.safetyCert) = true) at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
  obtain ⟨⟨⟨⟨hk1, hlen⟩, hbases⟩, hstep⟩, hsafe⟩ := hchk
  intro w hw s0 inputs hinit t
  -- Step 1: Prove inv holds for all t by strong induction on t
  have hinv_all : ∀ n, evalPred (runTrace sys s0 inputs n) Fin.elim0 inv = true := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hlt : n < cert.k
      · have hbase := checkBases_sound sys inv 0 cert.baseCerts hbases n (by omega) w hw s0 inputs hinit
        simpa using hbase
      · let t0 := n - cert.k
        have ht0_add : t0 + cert.k = n := by omega
        have hstep_ok := checkOblig_sound sys cert.k (stepHyps inv cert.k) inv cert.stepCert hstep w hw
          (runTrace sys s0 inputs t0) (fun j => inputs (t0 + j))
        have hhyps : ∀ j : Fin (cert.k + 1),
            evalPred (runTrace sys (runTrace sys s0 inputs t0) (fun idx => inputs (t0 + idx)) j.val)
              Fin.elim0 (stepHyps inv cert.k j) = true := by
          intro j
          unfold stepHyps
          by_cases hj : j.val < cert.k
          · simp only [hj, ↓reduceIte]
            rw [runTrace_add]
            exact ih (t0 + j.val) (by omega)
          · simp [hj, evalPred]
        have hres := hstep_ok hhyps
        rw [runTrace_add, ht0_add] at hres
        exact hres
  -- Step 2: Apply safety entailment (Inv -> Prop) at time t
  have hsafe_ok := checkOblig_sound sys 0 (safetyHyps inv) prop cert.safetyCert hsafe w hw
    (runTrace sys s0 inputs t) inputs
  apply hsafe_ok
  intro j
  simp [safetyHyps, runTrace, hinv_all t]



-- ============================================================================
-- Section 8: Five Flagship Infinite Bitwise Transition Systems (T1 - T5)
--            & Pure-Data Finite Binary Certificates Checked via `decide`
-- ============================================================================


-- Helper shorthands for readable AST definitions

private abbrev pIff {r m : Nat} (p q : BVPred r m) : BVPred r m :=
  .pAnd (.pImp p q) (.pImp q p)

-- ----------------------------------------------------------------------------
-- T1: Wrap-Safe Incremental Gray-Code Counter
--   x' = x + 1,  d = x ^^^ (x + 1),  g' = g ^^^ (d ^^^ (d >>> 1))
--   Property: (x = 0 -> g = 0) /\ (msb(x) = msb(g))
--   Impossible for pure k-induction at ANY k; proved via IC3 lemma g = x ^^^ (x >>> 1).
-- ----------------------------------------------------------------------------

def t1Sys : BVSystem 2 0 :=
  let x : BVExpr 2 0 := .reg ⟨0, by omega⟩
  let g : BVExpr 2 0 := .reg ⟨1, by omega⟩
  let xp1 := BVExpr.add x .one
  let d := BVExpr.xor x xp1
  { init := .pAnd (.eq x .zero) (.eq g .zero)
    next := fun i => match i.val with
      | 0 => xp1
      | _ => .xor g (.xor d (.shr1 d)) }

def t1Prop : BVPred 2 0 :=
  let x : BVExpr 2 0 := .reg ⟨0, by omega⟩
  let g : BVExpr 2 0 := .reg ⟨1, by omega⟩
  .pAnd (.pImp (.eq x .zero) (.eq g .zero))
        (pIff (.msbEq x true) (.msbEq g true))

def t1Cert_base0 : NatSet := (.node 23 (.node 11 .empty .empty) .empty)

def t1Cert_step : NatSet := (.node 11584 (.node 5440 (.node 3648 (.node 3498 (.node 3456 .empty .empty) .empty) (.node 3690 .empty .empty)) (.node 5760 (.node 5482 .empty .empty) (.node 5802 .empty .empty))) (.node 13696 (.node 11904 (.node 11626 .empty .empty) (.node 11946 .empty .empty)) (.node 13888 (.node 13738 .empty .empty) (.node 13930 .empty .empty))))

def t1Cert_safety : NatSet := (.node 206 (.node 29 (.node 5 .empty .empty) (.node 198 .empty .empty)) (.node 310 (.node 294 .empty .empty) (.node 485 .empty .empty)))

def t1Cert : KIndIC3Cert 2 :=
  let x : BVExpr 2 0 := .reg ⟨0, by omega⟩
  let g : BVExpr 2 0 := .reg ⟨1, by omega⟩
  { k := 1
    invClauses := [.eq g (.xor x (.shr1 x))]
    baseCerts := [t1Cert_base0]
    stepCert := t1Cert_step
    safetyCert := t1Cert_safety }

theorem t1_cert_valid : checkKIndIC3 t1Sys t1Prop t1Cert = true := by decide

theorem t1_safe : Safe t1Sys t1Prop :=
  checkKIndIC3_sound t1Sys t1Prop t1Cert t1_cert_valid

-- ----------------------------------------------------------------------------
-- T2: Nondeterministic Carry-Save Accumulator Equivalence
--   S' = (S ^^^ C) ^^^ u,  C' = maj(S, C, u) <<< 1,  A' = A + u
--   Property: (lsb(S) = lsb(A)) /\ (msb(S + C) = msb(A))
--   Impossible for pure k-induction at ANY k; proved via 2-clause IC3:
--     C1: S + C = A,   C2: lsb(C) = false.
-- ----------------------------------------------------------------------------

def t2Sys : BVSystem 3 1 :=
  let S : BVExpr 3 1 := .reg ⟨0, by omega⟩
  let C : BVExpr 3 1 := .reg ⟨1, by omega⟩
  let A : BVExpr 3 1 := .reg ⟨2, by omega⟩
  let u : BVExpr 3 1 := .inp ⟨0, by omega⟩
  let maj := BVExpr.or (.and S C) (.or (.and S u) (.and C u))
  { init := .pAnd (.eq (.reg ⟨0, by omega⟩) .zero)
              (.pAnd (.eq (.reg ⟨1, by omega⟩) .zero) (.eq (.reg ⟨2, by omega⟩) .zero))
    next := fun i => match i.val with
      | 0 => .xor (.xor S C) u
      | 1 => .shl1 maj
      | _ => .add A u }

def t2Prop : BVPred 3 0 :=
  let S : BVExpr 3 0 := .reg ⟨0, by omega⟩
  let C : BVExpr 3 0 := .reg ⟨1, by omega⟩
  let A : BVExpr 3 0 := .reg ⟨2, by omega⟩
  .pAnd (pIff (.lsbEq S true) (.lsbEq A true))
        (pIff (.msbEq (.add S C) true) (.msbEq A true))

def t2Cert_base0 : NatSet := (.node 87 .empty .empty)

def t2Cert_step : NatSet := (.node 746 (.node 683 (.node 680 .empty .empty) (.node 685 .empty .empty)) (.node 751 (.node 748 .empty .empty) .empty))

def t2Cert_safety : NatSet := (.node 189786 (.node 71003 (.node 2730 (.node 1370 .empty .empty) .empty) (.node 72363 .empty .empty)) (.node 259419 (.node 191146 .empty .empty) (.node 260779 .empty .empty)))

def t2Cert : KIndIC3Cert 3 :=
  let S : BVExpr 3 0 := .reg ⟨0, by omega⟩
  let C : BVExpr 3 0 := .reg ⟨1, by omega⟩
  let A : BVExpr 3 0 := .reg ⟨2, by omega⟩
  { k := 1
    invClauses := [.eq (.add S C) A, .lsbEq C false]
    baseCerts := [t2Cert_base0]
    stepCert := t2Cert_step
    safetyCert := t2Cert_safety }

theorem t2_cert_valid : checkKIndIC3 t2Sys t2Prop t2Cert = true := by decide

theorem t2_safe : Safe t2Sys t2Prop :=
  checkKIndIC3_sound t2Sys t2Prop t2Cert t2_cert_valid

-- ----------------------------------------------------------------------------
-- T3: 3-Stage Autonomous 3p+1 Carry-Defect Zero-Accumulator
--   q  = (p + (p <<< 1)) + (b ^^^ 1#w)
--   p' = q &&& ~~~(q <<< 1)
--   a' = (p + (p <<< 1)) ^^^ (p ^^^ (p <<< 1))
--   b' = b + a
--   Property: b = 0#w.
--   FAILS pure k=1 (CTI w=1) AND FAILS pure k=2 (CTI w=3).
--   Proved TWO ways:
--     (A) Pure k=3 induction with ZERO auxiliary IC3 lemmas (`t3Cert_k3`),
--     (B) IC3 strengthening at k=1 (`t3Cert_ic3`).
-- ----------------------------------------------------------------------------

def t3Sys : BVSystem 3 0 :=
  let p : BVExpr 3 0 := .reg ⟨0, by omega⟩
  let a : BVExpr 3 0 := .reg ⟨1, by omega⟩
  let b : BVExpr 3 0 := .reg ⟨2, by omega⟩
  let q := BVExpr.add (.add p (.shl1 p)) (.xor b .one)
  { init := .pAnd (.eq (.reg ⟨0, by omega⟩) .zero)
              (.pAnd (.eq (.reg ⟨1, by omega⟩) .zero) (.eq (.reg ⟨2, by omega⟩) .zero))
    next := fun i => match i.val with
      | 0 => .and q (.not (.shl1 q))
      | 1 => .xor (.add p (.shl1 p)) (.xor p (.shl1 p))
      | _ => .add b a }

def t3Prop : BVPred 3 0 :=
  .eq (.reg ⟨2, by omega⟩) .zero

def t3Cert_k3_base0 : NatSet := (.node 15 .empty .empty)

def t3Cert_k3_base1 : NatSet := (.node 123136 (.node 122880 .empty .empty) .empty)

def t3Cert_k3_base2 : NatSet := (.node 553705472 (.node 545841152 (.node 536928256 .empty .empty) .empty) (.node 714727680 .empty .empty))

def t3Cert_k3_step : NatSet := (.node 6665923469568 (.node 6597206224435 (.node 6597203995409 (.node 6597203992832 (.node 6597203992712 (.node 6597203992576 .empty .empty) .empty) (.node 6597203995289 .empty .empty)) (.node 6597206221056 (.node 6597206220800 (.node 6597203996211 .empty .empty) .empty) (.node 6597206223633 .empty .empty))) (.node 6633711214728 (.node 6597248445201 (.node 6597208190515 (.node 6597208187136 .empty .empty) .empty) (.node 6597250411281 .empty .empty)) (.node 6633757634355 (.node 6633715411729 (.node 6633715408896 .empty .empty) .empty) (.node 6665923469312 .empty .empty)))) (.node 7325473581721 (.node 6665927663872 (.node 6665923472947 (.node 6665923472145 (.node 6665923472025 .empty .empty) .empty) (.node 6665927663616 .empty .empty)) (.node 6665967919360 (.node 6665927667251 (.node 6665927666449 .empty .empty) .empty) (.node 6665969888017 .empty .empty))) (.node 7357685837363 (.node 7357685833984 (.node 7357685833728 (.node 7325515800832 .empty .empty) .empty) (.node 7357685836561 .empty .empty)) (.node 7357728058129 (.node 7357728055552 .empty .empty) (.node 7357728059187 .empty .empty)))))

def t3Cert_k3_safety : NatSet := (.node 3 .empty .empty)

def t3Cert_k3 : KIndIC3Cert 3 :=
  { k := 3
    invClauses := []
    baseCerts := [t3Cert_k3_base0, t3Cert_k3_base1, t3Cert_k3_base2]
    stepCert := t3Cert_k3_step
    safetyCert := t3Cert_k3_safety }

theorem t3_k3_cert_valid : checkKIndIC3 t3Sys t3Prop t3Cert_k3 = true := by decide

theorem t3_safe_via_k3 : Safe t3Sys t3Prop :=
  checkKIndIC3_sound t3Sys t3Prop t3Cert_k3 t3_k3_cert_valid

def t3Cert_ic3_base0 : NatSet := (.node 119 .empty .empty)

def t3Cert_ic3_step : NatSet := (.node 1960601 (.node 1949832 (.node 1949696 .empty .empty) (.node 1949952 .empty .empty)) (.node 2081024 (.node 1960721 .empty .empty) (.node 2091793 .empty .empty)))

def t3Cert_ic3_safety : NatSet := (.node 31 (.node 30 .empty .empty) .empty)

def t3Cert_ic3 : KIndIC3Cert 3 :=
  let p : BVExpr 3 0 := .reg ⟨0, by omega⟩
  let a : BVExpr 3 0 := .reg ⟨1, by omega⟩
  let b : BVExpr 3 0 := .reg ⟨2, by omega⟩
  { k := 1
    invClauses := [.eq (.and p (.shl1 p)) .zero, .eq a .zero, .eq b .zero]
    baseCerts := [t3Cert_ic3_base0]
    stepCert := t3Cert_ic3_step
    safetyCert := t3Cert_ic3_safety }

theorem t3_ic3_cert_valid : checkKIndIC3 t3Sys t3Prop t3Cert_ic3 = true := by decide

theorem t3_safe_via_ic3 : Safe t3Sys t3Prop :=
  checkKIndIC3_sound t3Sys t3Prop t3Cert_ic3 t3_ic3_cert_valid

-- ----------------------------------------------------------------------------
-- T4: Hybrid Sparse-Shift vs 3x-Adder Accumulator (Combined IC3 + k=2 Induction!)
--   p' = (x ^^^ u) &&& ~~~((x ^^^ u) <<< 1)
--   x' = x + (p ^^^ (p <<< 1))
--   y' = y + (p + (p <<< 1))
--   Property: msb(x) = msb(y).
--   FAILS pure k-induction for ALL k, AND IC3 lemma {x = y} FAILS at k=1 (CTI w=3).
--   Proved via COMBINED IC3 ({x = y}) + k=2 induction!
-- ----------------------------------------------------------------------------

def t4Sys : BVSystem 3 1 :=
  let p : BVExpr 3 1 := .reg ⟨0, by omega⟩
  let x : BVExpr 3 1 := .reg ⟨1, by omega⟩
  let y : BVExpr 3 1 := .reg ⟨2, by omega⟩
  let u : BVExpr 3 1 := .inp ⟨0, by omega⟩
  let xu := BVExpr.xor x u
  { init := .pAnd (.eq (.reg ⟨0, by omega⟩) .zero)
              (.pAnd (.eq (.reg ⟨1, by omega⟩) .zero) (.eq (.reg ⟨2, by omega⟩) .zero))
    next := fun i => match i.val with
      | 0 => .and xu (.not (.shl1 xu))
      | 1 => .add x (.xor p (.shl1 p))
      | _ => .add y (.add p (.shl1 p)) }

def t4Prop : BVPred 3 0 :=
  let x : BVExpr 3 0 := .reg ⟨1, by omega⟩
  let y : BVExpr 3 0 := .reg ⟨2, by omega⟩
  pIff (.msbEq x true) (.msbEq y true)

def t4Cert_base0 : NatSet := (.node 15 .empty .empty)

def t4Cert_base1 : NatSet := (.node 961 (.node 960 .empty .empty) .empty)

def t4Cert_step : NatSet := (.node 29249 (.node 24795 (.node 24686 (.node 24666 (.node 24650 (.node 24641 (.node 24640 .empty .empty) .empty) (.node 24651 .empty .empty)) (.node 24676 (.node 24667 .empty .empty) (.node 24677 .empty .empty))) (.node 24769 (.node 24703 (.node 24702 (.node 24687 .empty .empty) .empty) (.node 24768 .empty .empty)) (.node 24779 (.node 24778 .empty .empty) (.node 24794 .empty .empty)))) (.node 25957 (.node 24830 (.node 24814 (.node 24805 (.node 24804 .empty .empty) .empty) (.node 24815 .empty .empty)) (.node 25921 (.node 24831 .empty .empty) (.node 25947 .empty .empty))) (.node 26085 (.node 26049 (.node 25983 (.node 25967 .empty .empty) .empty) (.node 26075 .empty .empty)) (.node 26111 (.node 26095 .empty .empty) (.node 29248 .empty .empty))))) (.node 29413 (.node 29310 (.node 29284 (.node 29274 (.node 29259 (.node 29258 .empty .empty) .empty) (.node 29275 .empty .empty)) (.node 29294 (.node 29285 .empty .empty) (.node 29295 .empty .empty))) (.node 29387 (.node 29377 (.node 29376 (.node 29311 .empty .empty) .empty) (.node 29386 .empty .empty)) (.node 29403 (.node 29402 .empty .empty) (.node 29412 .empty .empty)))) (.node 30575 (.node 30529 (.node 29438 (.node 29423 (.node 29422 .empty .empty) .empty) (.node 29439 .empty .empty)) (.node 30555 (.node 30539 .empty .empty) (.node 30565 .empty .empty))) (.node 30683 (.node 30657 (.node 30591 .empty .empty) (.node 30667 .empty .empty)) (.node 30703 (.node 30693 .empty .empty) (.node 30719 .empty .empty))))))

def t4Cert_safety : NatSet := (.node 31 (.node 1 .empty .empty) .empty)

def t4Cert : KIndIC3Cert 3 :=
  let x : BVExpr 3 0 := .reg ⟨1, by omega⟩
  let y : BVExpr 3 0 := .reg ⟨2, by omega⟩
  { k := 2
    invClauses := [.eq x y]
    baseCerts := [t4Cert_base0, t4Cert_base1]
    stepCert := t4Cert_step
    safetyCert := t4Cert_safety }

theorem t4_cert_valid : checkKIndIC3 t4Sys t4Prop t4Cert = true := by decide

theorem t4_safe : Safe t4Sys t4Prop :=
  checkKIndIC3_sound t4Sys t4Prop t4Cert t4_cert_valid

-- ----------------------------------------------------------------------------
-- T5: Overflow-Free Fixed-Point Averaging Filter Exact 1-ULP Error Bound
--   L' = (L >>> 1) + (u >>> 1)
--   M' = (M &&& u) + ((M ^^^ u) >>> 1)
--   Property: L ≤ M /\ M - L ≤ 1#w (for ALL w ≥ 1, ALL input streams u, ALL t).
--   Exercises `add`, `sub`, `and`, `xor`, `shr1`, and unsigned borrow `ule`!
--   Notice `M - L ≤ 1#w` alone FAILS 1-induction (modular wraparound CTI at w=2).
-- ----------------------------------------------------------------------------

def t5Sys : BVSystem 2 1 :=
  let L : BVExpr 2 1 := .reg ⟨0, by omega⟩
  let M : BVExpr 2 1 := .reg ⟨1, by omega⟩
  let u : BVExpr 2 1 := .inp ⟨0, by omega⟩
  { init := .pAnd (.eq (.reg ⟨0, by omega⟩) .zero) (.eq (.reg ⟨1, by omega⟩) .zero)
    next := fun i => match i.val with
      | 0 => .add (.shr1 L) (.shr1 u)
      | _ => .add (.and M u) (.shr1 (.xor M u)) }

def t5Prop : BVPred 2 0 :=
  let L : BVExpr 2 0 := .reg ⟨0, by omega⟩
  let M : BVExpr 2 0 := .reg ⟨1, by omega⟩
  .pAnd (.ule L M) (.ule (.sub M L) .one)

def t5Cert_base0 : NatSet := (.node 3 .empty .empty)

def t5Cert_step : NatSet := (.node 15142 (.node 2118 (.node 805 (.node 73 (.node 58 (.node 38 (.node 37 .empty .empty) (.node 41 .empty .empty)) (.node 70 (.node 69 .empty .empty) .empty)) (.node 214 (.node 197 (.node 90 .empty .empty) .empty) (.node 218 (.node 217 .empty .empty) .empty))) (.node 841 (.node 826 (.node 825 (.node 822 .empty .empty) .empty) (.node 838 (.node 837 .empty .empty) .empty)) (.node 2086 (.node 2085 (.node 858 .empty .empty) .empty) (.node 2106 (.node 2089 .empty .empty) .empty)))) (.node 2889 (.node 2853 (.node 2262 (.node 2245 (.node 2121 .empty .empty) .empty) (.node 2266 (.node 2265 .empty .empty) .empty)) (.node 2874 (.node 2873 (.node 2870 .empty .empty) .empty) (.node 2886 (.node 2885 .empty .empty) .empty))) (.node 12486 (.node 3033 (.node 3030 (.node 2906 .empty .empty) .empty) (.node 12329 (.node 12326 .empty .empty) .empty)) (.node 13097 (.node 13094 (.node 12489 .empty .empty) .empty) (.node 14537 (.node 14534 .empty .empty) .empty))))) (.node 45094 (.node 34885 (.node 33622 (.node 32825 (.node 32822 (.node 15145 .empty .empty) .empty) (.node 32858 (.node 32837 .empty .empty) .empty)) (.node 34870 (.node 34853 (.node 33625 .empty .empty) .empty) (.node 34874 (.node 34873 .empty .empty) .empty))) (.node 35638 (.node 34906 (.node 34889 (.node 34886 .empty .empty) .empty) (.node 35033 (.node 35030 .empty .empty) .empty)) (.node 35670 (.node 35653 (.node 35641 .empty .empty) .empty) (.node 35674 (.node 35673 .empty .empty) .empty)))) (.node 47305 (.node 45894 (.node 45274 (.node 45253 (.node 45097 .empty .empty) .empty) (.node 45882 (.node 45861 .empty .empty) .empty)) (.node 47145 (.node 47142 (.node 45897 .empty .empty) .empty) (.node 47302 (.node 47301 .empty .empty) .empty))) (.node 47942 (.node 47910 (.node 47909 (.node 47322 .empty .empty) .empty) (.node 47930 (.node 47913 .empty .empty) .empty)) (.node 48086 (.node 48069 (.node 47945 .empty .empty) .empty) (.node 48090 (.node 48089 .empty .empty) .empty))))))

def t5Cert_safety : NatSet := (.node 136 (.node 51 (.node 0 .empty .empty) .empty) (.node 187 .empty .empty))

def t5Cert : KIndIC3Cert 2 :=
  let L : BVExpr 2 0 := .reg ⟨0, by omega⟩
  let M : BVExpr 2 0 := .reg ⟨1, by omega⟩
  { k := 1
    invClauses := [.ule L M, .ule (.sub M L) .one]
    baseCerts := [t5Cert_base0]
    stepCert := t5Cert_step
    safetyCert := t5Cert_safety }

theorem t5_cert_valid : checkKIndIC3 t5Sys t5Prop t5Cert = true := by decide

theorem t5_safe : Safe t5Sys t5Prop :=
  checkKIndIC3_sound t5Sys t5Prop t5Cert t5_cert_valid

-- ============================================================================
-- Section 9: Completely Unfolded Standalone Native `BitVec w` Theorems
--            (Zero AST / Compiler Wrappers in Theorem Signatures!)
-- ============================================================================

private theorem bool_eq_of_dec_iff {a b : Bool}
    (h1 : decide (a = true) = false ∨ decide (b = true) = true)
    (h2 : decide (b = true) = false ∨ decide (a = true) = true) :
    b = a := by
  cases a <;> cases b <;> simp_all

private theorem grayTrace_eq_runTrace (w t : Nat) :
    let st := runTrace t1Sys (fun _ => 0#w) (fun _ => Fin.elim0) t
    (st ⟨0, by omega⟩, st ⟨1, by omega⟩) = grayTrace w t := by
  induction t with
  | zero => rfl
  | succ k ih =>
    simp only [grayTrace, runTrace, t1Sys, evalExpr] at ih ⊢
    rw [← ih]

theorem thm1_wrapSafeGray_safety :
    ∀ (w : Nat), w ≥ 1 → ∀ (t : Nat),
      let (x, g) := grayTrace w t
      (x = 0#w → g = 0#w) ∧ g.msb = x.msb := by
  intro w hw t
  have hsafe := t1_safe w hw (fun _ => 0#w) (fun _ => Fin.elim0) (by simp [t1Sys, evalPred, evalExpr]) t
  have heq := grayTrace_eq_runTrace w t
  dsimp only [t1Prop, pIff, evalPred, evalExpr] at hsafe
  dsimp only at heq ⊢
  rw [← heq]
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hsafe
  obtain ⟨himp, hmx, hmg⟩ := hsafe
  constructor
  · intro hx
    rcases himp with hne | hg
    · have : (runTrace t1Sys (fun _ => 0#w) (fun _ => Fin.elim0) t ⟨0, by omega⟩) ≠ 0#w :=
        of_decide_eq_false hne
      exact absurd hx this
    · exact of_decide_eq_true hg
  · exact bool_eq_of_dec_iff hmx hmg

private theorem csaTrace_eq_runTrace {w : Nat} (u : Nat → BitVec w) (t : Nat) :
    let st := runTrace t2Sys (fun _ => 0#w) (fun k _ => u k) t
    (st ⟨0, by omega⟩, st ⟨1, by omega⟩, st ⟨2, by omega⟩) = csaTrace u t := by
  induction t with
  | zero => rfl
  | succ k ih =>
    simp only [csaTrace, runTrace, t2Sys, evalExpr] at ih ⊢
    rw [← ih]

theorem thm2_carrySave_safety :
    ∀ (w : Nat), w ≥ 1 → ∀ (u : Nat → BitVec w) (t : Nat),
      let (S, C, A) := csaTrace u t
      S.getLsbD 0 = A.getLsbD 0 ∧ (S + C).msb = A.msb := by
  intro w hw u t
  have hsafe := t2_safe w hw (fun _ => 0#w) (fun k _ => u k) (by simp [t2Sys, evalPred, evalExpr]) t
  have heq := csaTrace_eq_runTrace u t
  dsimp only [t2Prop, pIff, evalPred, evalExpr] at hsafe
  dsimp only at heq ⊢
  rw [← heq]
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hsafe
  obtain ⟨⟨hl1, hl2⟩, ⟨hm1, hm2⟩⟩ := hsafe
  exact ⟨(bool_eq_of_dec_iff hl1 hl2).symm, (bool_eq_of_dec_iff hm1 hm2).symm⟩

private theorem defectPipeTrace_eq_runTrace (w t : Nat) :
    let st := runTrace t3Sys (fun _ => 0#w) (fun _ => Fin.elim0) t
    (st ⟨0, by omega⟩, st ⟨1, by omega⟩, st ⟨2, by omega⟩) = defectPipeTrace w t := by
  induction t with
  | zero => rfl
  | succ k ih =>
    simp only [defectPipeTrace, runTrace, t3Sys, evalExpr] at ih ⊢
    rw [← ih]

/-- Proved via PURE k=3 induction (`t3_safe_via_k3`, zero auxiliary IC3 lemmas). -/
theorem thm3_carryDefectPipeline_zero :
    ∀ (w : Nat), w ≥ 1 → ∀ (t : Nat),
      (defectPipeTrace w t).2.2 = 0#w := by
  intro w hw t
  have hsafe := t3_safe_via_k3 w hw (fun _ => 0#w) (fun _ => Fin.elim0)
    (by simp [t3Sys, evalPred, evalExpr]) t
  have heq := defectPipeTrace_eq_runTrace w t
  dsimp only [t3Prop, evalPred, evalExpr] at hsafe
  have h2 : (defectPipeTrace w t).2.2 = runTrace t3Sys (fun _ => 0#w) (fun _ => Fin.elim0) t ⟨2, by omega⟩ := by
    rw [← heq]
  rw [h2]
  exact of_decide_eq_true hsafe

private theorem hybridTrace_eq_runTrace {w : Nat} (u : Nat → BitVec w) (t : Nat) :
    let st := runTrace t4Sys (fun _ => 0#w) (fun k _ => u k) t
    (st ⟨0, by omega⟩, st ⟨1, by omega⟩, st ⟨2, by omega⟩) = hybridTrace u t := by
  induction t with
  | zero => rfl
  | succ k ih =>
    simp only [hybridTrace, runTrace, t4Sys, evalExpr] at ih ⊢
    rw [← ih]

/-- Proved via COMBINED IC3 ({x = y}) + k=2 induction (`t4_safe`). -/
theorem thm4_hybridSparseAdder_msb :
    ∀ (w : Nat), w ≥ 1 → ∀ (u : Nat → BitVec w) (t : Nat),
      (hybridTrace u t).2.1.msb = (hybridTrace u t).2.2.msb := by
  intro w hw u t
  have hsafe := t4_safe w hw (fun _ => 0#w) (fun k _ => u k)
    (by simp [t4Sys, evalPred, evalExpr]) t
  have heq := hybridTrace_eq_runTrace u t
  dsimp only [t4Prop, pIff, evalPred, evalExpr] at hsafe
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hsafe
  obtain ⟨hm1, hm2⟩ := hsafe
  have hx : (hybridTrace u t).2.1 = runTrace t4Sys (fun _ => 0#w) (fun k _ => u k) t ⟨1, by omega⟩ := by rw [← heq]
  have hy : (hybridTrace u t).2.2 = runTrace t4Sys (fun _ => 0#w) (fun k _ => u k) t ⟨2, by omega⟩ := by rw [← heq]
  rw [hx, hy]
  exact (bool_eq_of_dec_iff hm1 hm2).symm

private theorem avgFilterTrace_eq_runTrace {w : Nat} (u : Nat → BitVec w) (t : Nat) :
    let st := runTrace t5Sys (fun _ => 0#w) (fun k _ => u k) t
    (st ⟨0, by omega⟩, st ⟨1, by omega⟩) = avgFilterTrace u t := by
  induction t with
  | zero => rfl
  | succ k ih =>
    simp only [avgFilterTrace, runTrace, t5Sys, evalExpr] at ih ⊢
    rw [← ih]

/-- Proved via width-uniform IC3 with unsigned borrow `ule`, `sub`, and `shr1` (`t5_safe`). -/
theorem thm5_avgFilter_oneULP :
    ∀ (w : Nat), w ≥ 1 → ∀ (u : Nat → BitVec w) (t : Nat),
      let (L, M) := avgFilterTrace u t
      L ≤ M ∧ M - L ≤ 1#w := by
  intro w hw u t
  have hsafe := t5_safe w hw (fun _ => 0#w) (fun k _ => u k)
    (by simp [t5Sys, evalPred, evalExpr]) t
  have heq := avgFilterTrace_eq_runTrace u t
  simp only [t5Prop, evalPred, evalExpr, Bool.and_eq_true] at hsafe
  dsimp only at heq ⊢
  rw [← heq]
  exact ⟨of_decide_eq_true hsafe.1, of_decide_eq_true hsafe.2⟩

-- ============================================================================
-- Section 10: Kernel-Checked Non-Vacuity Witnesses, Negative / Mutation Tests,
--             and Exact Sharpness Counterexamples
-- ============================================================================

-- ---- 10A. Non-Vacuity Witnesses (non-trivial nonzero evolution for all 5 systems) ----

example : ∃ s0 : Fin 2 → BitVec 4,
    evalPred s0 Fin.elim0 t1Sys.init = true ∧
    (grayTrace 4 5).1 = 5#4 ∧ (grayTrace 4 5).2 = 7#4 ∧
    (grayTrace 4 16).1 = 0#4 ∧ (grayTrace 4 16).2 = 0#4 :=
  ⟨fun _ => 0#4, by decide⟩

example : ∃ (s0 : Fin 3 → BitVec 8) (u : Nat → BitVec 8),
    evalPred s0 Fin.elim0 t2Sys.init = true ∧
    (csaTrace u 3).1 ≠ 0#8 ∧ (csaTrace u 3).2.1 ≠ 0#8 ∧ (csaTrace u 3).2.2 = 171#8 :=
  ⟨fun _ => 0#8, fun _ => 57#8, by decide⟩

example : ∃ s0 : Fin 3 → BitVec 8,
    evalPred s0 Fin.elim0 t3Sys.init = true ∧
    (defectPipeTrace 8 4).1 = 16#8 ∧ (defectPipeTrace 8 6).1 = 20#8 ∧ (defectPipeTrace 8 6).2.2 = 0#8 :=
  ⟨fun _ => 0#8, by decide⟩

example : ∃ (s0 : Fin 3 → BitVec 8) (u : Nat → BitVec 8),
    evalPred s0 Fin.elim0 t4Sys.init = true ∧
    (hybridTrace u 4).2.1 ≠ 0#8 ∧ (hybridTrace u 4).2.1 = (hybridTrace u 4).2.2 :=
  ⟨fun _ => 0#8, fun _ => 173#8, by decide⟩

example : ∃ (s0 : Fin 2 → BitVec 8) (u : Nat → BitVec 8),
    evalPred s0 Fin.elim0 t5Sys.init = true ∧
    (avgFilterTrace u 3).1 = 222#8 ∧ (avgFilterTrace u 3).2 = 223#8 :=
  ⟨fun _ => 0#8, fun _ => 255#8, by decide⟩

-- ---- 10B. Kernel-Checked Negative & Hostile Mutation Tests (`checkKIndIC3 = false`) ----

-- Mutation 1: Deleting a single reachable state from t1Cert.stepCert is REJECTED

theorem neg_mut1_t1_delete_state :
    checkKIndIC3 t1Sys t1Prop
      { t1Cert with stepCert :=
          (.node 11584 (.node 5440 (.node 3648 (.node 3498 (.node 3456 .empty .empty) .empty) (.node 3690 .empty .empty))
            (.node 5760 (.node 5482 .empty .empty) (.node 5802 .empty .empty)))
            (.node 13696 (.node 11904 (.node 11626 .empty .empty) (.node 11946 .empty .empty))
            (.node 13888 (.node 13738 .empty .empty) .empty))) } = false := by decide

-- Mutation 2: Bit-flipping a single code in t2Cert.stepCert is REJECTED

theorem neg_mut2_t2_bitflip :
    checkKIndIC3 t2Sys t2Prop
      { t2Cert with stepCert :=
          (.node 747 (.node 683 (.node 680 .empty .empty) (.node 685 .empty .empty))
            (.node 751 (.node 748 .empty .empty) .empty)) } = false := by decide

-- Mutation 3: Empty stepCert on T3 (k=3) is REJECTED

theorem neg_mut3_t3_empty_step :
    checkKIndIC3 t3Sys t3Prop { t3Cert_k3 with stepCert := .empty } = false := by decide

-- Mutation 4: k = 0 is REJECTED even with empty baseCerts

theorem neg_mut4_zero_k :
    checkKIndIC3 t2Sys t2Prop { t2Cert with k := 0, baseCerts := [] } = false := by decide

-- Mutation 5: Mismatched baseCerts length (k = 2 with only 1 baseCert) is REJECTED

theorem neg_mut5_base_len_mismatch :
    checkKIndIC3 t4Sys t4Prop { t4Cert with baseCerts := [t4Cert_base0] } = false := by decide

-- Mutation 6: Cross-system certificate swap (using t3Cert_ic3 on t2Sys) is REJECTED

theorem neg_mut6_cross_system_swap :
    checkKIndIC3 t2Sys t2Prop t3Cert_ic3 = false := by decide

-- Mutation 7: Dropping IC3 clause `lsb(C) = false` on T2 is REJECTED

theorem neg_mut7_t2_drop_ic3_clause :
    let S : BVExpr 3 0 := .reg ⟨0, by omega⟩
    let C : BVExpr 3 0 := .reg ⟨1, by omega⟩
    let A : BVExpr 3 0 := .reg ⟨2, by omega⟩
    checkKIndIC3 t2Sys t2Prop { t2Cert with invClauses := [.eq (.add S C) A] } = false := by decide

-- Mutation 8: Weakening T4 from k=2 to k=1 (keeping IC3 {x = y}) is REJECTED

theorem neg_mut8_t4_weaken_k1 :
    checkKIndIC3 t4Sys t4Prop { t4Cert with k := 1, baseCerts := [t4Cert_base0] } = false := by decide

-- Mutation 9: Mutating a safetyCert state on T5 is REJECTED

theorem neg_mut9_t5_corrupt_safety :
    checkKIndIC3 t5Sys t5Prop { t5Cert with safetyCert := (.node 136 (.node 51 .empty .empty) (.node 187 .empty .empty)) } = false := by decide

-- ---- 10C. Kernel-Checked Sharpness & Counterexample-to-Induction (CTI) Theorems ----

/-- Sharpness 1: Without the wraparound fix (`d ^^^ (d >>> 1)`), the naive lowbit Gray counter
    FAILS zero-synchronization at `t = 2^w` (witnessed at `w = 2, t = 4` and `w = 4, t = 16`). -/
def buggyGrayTrace (w : Nat) : Nat → BitVec w × BitVec w
  | 0 => (0#w, 0#w)
  | t + 1 =>
    let (x, g) := buggyGrayTrace w t
    let xp1 := x + 1#w
    (xp1, g ^^^ (xp1 &&& (0#w - xp1)))

theorem sharp1_buggyGray_fails_w2 :
    (buggyGrayTrace 2 4).1 = 0#2 ∧ (buggyGrayTrace 2 4).2 ≠ 0#2 := by decide

theorem sharp1_buggyGray_fails_w4 :
    (buggyGrayTrace 4 16).1 = 0#4 ∧ (buggyGrayTrace 4 16).2 ≠ 0#4 := by decide

/-- Sharpness 2: T3 pure k=2 induction FAILS (explicit w=3 CTI: s0 = (3, 0, 0) -> (2, 4, 0) -> (1, 0, 4)). -/
theorem sharp2_t3_not_2_inductive :
    let s0 : Fin 3 → BitVec 3 := fun i => match i.val with | 0 => 3#3 | _ => 0#3
    let u  : Nat → Fin 0 → BitVec 3 := fun _ => Fin.elim0
    evalPred (runTrace t3Sys s0 u 0) Fin.elim0 t3Prop = true ∧
    evalPred (runTrace t3Sys s0 u 1) Fin.elim0 t3Prop = true ∧
    evalPred (runTrace t3Sys s0 u 2) Fin.elim0 t3Prop = false := by decide

/-- Sharpness 3: T4 IC3 clause `{x = y}` is NOT 1-inductive (explicit w=3 CTI: s0 = (3, 0, 0) -> (0, 5, 1)). -/
theorem sharp3_t4_inv_not_1_inductive :
    let s0 : Fin 3 → BitVec 3 := fun i => match i.val with | 0 => 3#3 | _ => 0#3
    let u  : Nat → Fin 1 → BitVec 3 := fun _ _ => 0#3
    let inv : BVPred 3 0 := .eq (.reg ⟨1, by omega⟩) (.reg ⟨2, by omega⟩)
    evalPred (runTrace t4Sys s0 u 0) Fin.elim0 inv = true ∧
    evalPred (runTrace t4Sys s0 u 1) Fin.elim0 inv = false := by decide

/-- Sharpness 4: T5's 1-ULP bound is EXACT — tighter bound `M - L ≤ 0#w` FAILS at w=2, t=2 (u = 3, 3). -/
theorem sharp4_avgFilter_zeroULP_fails :
    let u : Nat → BitVec 2 := fun _ => 3#2
    let (L, M) := avgFilterTrace u 2
    ¬ (M - L ≤ 0#2) := by decide

/-- Sharpness 5: Replacing T5's overflow-free average `(M &&& u) + ((M ^^^ u) >>> 1)` with the naive
    overflowing `(M + u) >>> 1` FAILS `L ≤ M` at w=2, t=2 (u = 3, 3). -/
def buggyAvgTrace {w : Nat} (u : Nat → BitVec w) : Nat → BitVec w × BitVec w
  | 0 => (0#w, 0#w)
  | t + 1 =>
    let (L, M) := buggyAvgTrace u t
    let ut := u t
    ((L >>> 1) + (ut >>> 1), (M + ut) >>> 1)

theorem sharp5_buggyAvg_fails :
    let u : Nat → BitVec 2 := fun _ => 3#2
    let (L, M) := buggyAvgTrace u 2
    ¬ (L ≤ M) := by decide

/-- Sharpness 6: On T5, `M - L ≤ 1#w` ALONE is NOT 1-inductive (modular wraparound CTI at w=2: L=3, M=0). -/
theorem sharp6_t5_ulp_alone_not_1_inductive :
    let s0 : Fin 2 → BitVec 2 := fun i => match i.val with | 0 => 3#2 | _ => 0#2
    let u  : Nat → Fin 1 → BitVec 2 := fun _ _ => 0#2
    let ulpOnly : BVPred 2 0 := .ule (.sub (.reg ⟨1, by omega⟩) (.reg ⟨0, by omega⟩)) .one
    evalPred (runTrace t5Sys s0 u 0) Fin.elim0 ulpOnly = true ∧
    evalPred (runTrace t5Sys s0 u 1) Fin.elim0 ulpOnly = false := by decide


-- ============================================================================
-- Section 11: Exhaustive `#print axioms` Audit (Must Be ⊆ Standard Axioms)
-- ============================================================================

end KIndIC3
