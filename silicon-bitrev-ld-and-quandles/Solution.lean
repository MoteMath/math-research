/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Defs

/-!
# Verified Proofs: Pure-Silicon Bit-Reversal LD-Systems and Non-Alexander XOR-Carry Knot Quandles

Zero-dependency pure-Init Lean 4.34.1 proofs of all 10 theorems in `Challenge.lean`.
-/

namespace SiliconLDQuandles

/-! ## Part I: Partial-Involution LD-Systems -/

theorem partialInvLD_idemp {α : Type u} (τ : α → Option α) (X : α → Bool) :
    partialInvLD τ X X = X := by
  funext i
  simp only [partialInvLD]
  cases h : τ i with
  | none => simp
  | some j => cases X j <;> simp

theorem partialInvLD_left_distrib {α : Type u} (τ : α → Option α)
    (hτ : IsPartialInvolution τ) (X Y Z : α → Bool) :
    partialInvLD τ X (partialInvLD τ Y Z) =
      partialInvLD τ (partialInvLD τ X Y) (partialInvLD τ X Z) := by
  funext i
  cases hti : τ i with
  | none =>
    simp only [partialInvLD, hti]
    cases X i <;> simp
  | some j =>
    have htj : τ j = some i := hτ i j hti
    simp only [partialInvLD, hti, htj]
    cases X i <;> cases X j <;> cases Y i <;> cases Y j <;> cases Z i <;> cases Z j <;> simp

theorem partialInvLD_flexible {α : Type u} (τ : α → Option α)
    (hτ : IsPartialInvolution τ) (X Y : α → Bool) :
    partialInvLD τ (partialInvLD τ X Y) X = partialInvLD τ X (partialInvLD τ Y X) := by
  funext i
  cases hti : τ i with
  | none =>
    simp only [partialInvLD, hti]
    cases X i <;> simp
  | some j =>
    have htj : τ j = some i := hτ i j hti
    simp only [partialInvLD, hti, htj]
    cases X i <;> cases X j <;> cases Y i <;> cases Y j <;> simp

theorem partialInvLD_non_assoc_non_comm {α : Type u} [DecidableEq α] (τ : α → Option α)
    (hτ : IsPartialInvolution τ) {a b : α} (hab : a ≠ b) (hτa : τ a = some b) :
    (∃ X Y Z : α → Bool,
      partialInvLD τ (partialInvLD τ X Y) Z ≠ partialInvLD τ X (partialInvLD τ Y Z)) ∧
    (∃ X Y : α → Bool, partialInvLD τ X Y ≠ partialInvLD τ Y X) := by
  have hτb : τ b = some a := hτ a b hτa
  have hba : b ≠ a := hab.symm
  let sa : α → Bool := fun i => decide (i = a)
  let empty : α → Bool := fun _ => false
  constructor
  · refine ⟨empty, empty, sa, ?_⟩
    intro heq
    have hv := congrFun heq a
    simp [partialInvLD, hτa, hτb, sa, empty, hba] at hv
  · refine ⟨empty, sa, ?_⟩
    intro heq
    have hv := congrFun heq a
    simp [partialInvLD, hτa, sa, empty, hba] at hv

/-! ## Part II: Shifted Bit-Reversal LD-System Realization on `BitVec w` -/

private theorem nat_add_eq_or_of_and_zero (a b : Nat) (h : (a &&& b) = 0) :
    a + b = (a ||| b) := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha0 : a = 0
    · subst ha0; simp
    · have hbit0 : ¬(a % 2 = 1 ∧ b % 2 = 1) := by
        rintro ⟨ha1, hb1⟩
        have hb := congrArg (fun x => x.testBit 0) h
        rw [Nat.testBit_and] at hb
        simp [Nat.testBit_zero, ha1, hb1] at hb
      have hdiv_and : ((a / 2) &&& (b / 2)) = 0 := by
        apply Nat.eq_of_testBit_eq; intro r
        have hb := congrArg (fun x => x.testBit (r + 1)) h
        rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, Nat.zero_testBit] at hb
        rw [Nat.testBit_and, Nat.zero_testBit]; exact hb
      have hih := ih (a / 2) (by omega) (b / 2) hdiv_and
      apply Nat.eq_of_testBit_eq; intro r
      cases r with
      | zero =>
        rw [Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
        rcases Nat.mod_two_eq_zero_or_one a with ha2 | ha2 <;>
          rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2
        · have : (a + b) % 2 = 0 := by omega
          simp [this, ha2, hb2]
        · have : (a + b) % 2 = 1 := by omega
          simp [this, ha2, hb2]
        · have : (a + b) % 2 = 1 := by omega
          simp [this, ha2, hb2]
        · exact absurd ⟨ha2, hb2⟩ hbit0
      | succ r =>
        rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
        have hdiv_sum : (a + b) / 2 = a / 2 + b / 2 := by
          rcases Nat.mod_two_eq_zero_or_one a with ha2 | ha2 <;>
            rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2 <;> omega
        rw [hdiv_sum, hih, Nat.testBit_or]

theorem bitrevShiftOp_eq_add (w s : Nat) (x y : BitVec w) :
    bitrevShiftOp w s x y = x + (((bitrev w (y &&& ~~~x)) <<< s) &&& ~~~x) := by
  let t : BitVec w := (bitrev w (y &&& ~~~x)) <<< s
  have hor : x ||| t = x ||| (t &&& ~~~x) := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [hi]
    cases x[i] <;> cases t[i] <;> rfl
  have hand0 : (x.toNat &&& (t &&& ~~~x).toNat) = 0 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hr : r < w
    · rw [BitVec.testBit_toNat, BitVec.testBit_toNat]
      simp [hr]
      cases x[r] <;> simp
    · rw [BitVec.testBit_toNat]
      have hx : x.getLsbD r = false := BitVec.getLsbD_of_ge x r (by omega)
      simp [hx]
  have hadd_nat : x.toNat + (t &&& ~~~x).toNat = (x.toNat ||| (t &&& ~~~x).toNat) :=
    nat_add_eq_or_of_and_zero x.toNat (t &&& ~~~x).toNat hand0
  have hlt : (x.toNat ||| (t &&& ~~~x).toNat) < 2 ^ w := by
    rw [← BitVec.toNat_or]; exact (x ||| (t &&& ~~~x)).isLt
  unfold bitrevShiftOp
  change x ||| t = x + (t &&& ~~~x)
  rw [hor]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_or, hadd_nat, Nat.mod_eq_of_lt hlt]

private def shiftRevTau (w s : Nat) (i : Fin w) : Option (Fin w) :=
  if h : s ≤ i.1 then
    some ⟨w - 1 - (i.1 - s), by omega⟩
  else
    none

private theorem shiftRevTau_inv (w s : Nat) : IsPartialInvolution (shiftRevTau w s) := by
  intro a b h
  unfold shiftRevTau at h ⊢
  split at h
  · rename_i ha
    injection h with hb
    subst hb
    have hb_ge : s ≤ w - 1 - (a.1 - s) := by omega
    simp only [hb_ge, ↓reduceDIte]
    congr 1; ext; dsimp only; omega
  · cases h

private theorem bitrevShiftOp_getLsbD (w s : Nat) (x y : BitVec w) (i : Fin w) :
    (bitrevShiftOp w s x y).getLsbD i.1 =
      partialInvLD (shiftRevTau w s) (fun k => x.getLsbD k.1) (fun k => y.getLsbD k.1) i := by
  unfold bitrevShiftOp bitrev partialInvLD shiftRevTau
  rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  by_cases h : s ≤ i.1
  · simp only [h, ↓reduceDIte]
    have hlt : i.1 - s < w := by omega
    have hge : ¬(i.1 < s) := by omega
    have hi_lt : i.1 < w := i.isLt
    have hidx : w - 1 - (i.1 - s) < w := by omega
    rw [BitVec.getLsbD_reverse]
    simp [hi_lt, hge, hlt, BitVec.getMsbD, hidx]
  · simp only [h, ↓reduceDIte]
    have hlt : i.1 < s := by omega
    simp [hlt]

theorem bitrevShiftOp_ld_laws (w s : Nat) :
    (∀ x : BitVec w, bitrevShiftOp w s x x = x) ∧
    (∀ x y z : BitVec w,
      bitrevShiftOp w s x (bitrevShiftOp w s y z) =
        bitrevShiftOp w s (bitrevShiftOp w s x y) (bitrevShiftOp w s x z)) ∧
    (∀ x y : BitVec w,
      bitrevShiftOp w s (bitrevShiftOp w s x y) x =
        bitrevShiftOp w s x (bitrevShiftOp w s y x)) ∧
    (s + 2 ≤ w →
      (∃ x y z : BitVec w,
        bitrevShiftOp w s (bitrevShiftOp w s x y) z ≠
          bitrevShiftOp w s x (bitrevShiftOp w s y z)) ∧
      (∃ x y : BitVec w, bitrevShiftOp w s x y ≠ bitrevShiftOp w s y x)) := by
  have hτ := shiftRevTau_inv w s
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have h1 := bitrevShiftOp_getLsbD w s x x ⟨i, hi⟩
    rw [partialInvLD_idemp] at h1
    exact h1
  · intro x y z
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hL := bitrevShiftOp_getLsbD w s x (bitrevShiftOp w s y z) ⟨i, hi⟩
    have hR := bitrevShiftOp_getLsbD w s (bitrevShiftOp w s x y) (bitrevShiftOp w s x z) ⟨i, hi⟩
    have hsub : (fun k : Fin w => (bitrevShiftOp w s y z).getLsbD k.1) =
        partialInvLD (shiftRevTau w s) (fun k => y.getLsbD k.1) (fun k => z.getLsbD k.1) := by
      funext k; exact bitrevShiftOp_getLsbD w s y z k
    have hsub1 : (fun k : Fin w => (bitrevShiftOp w s x y).getLsbD k.1) =
        partialInvLD (shiftRevTau w s) (fun k => x.getLsbD k.1) (fun k => y.getLsbD k.1) := by
      funext k; exact bitrevShiftOp_getLsbD w s x y k
    have hsub2 : (fun k : Fin w => (bitrevShiftOp w s x z).getLsbD k.1) =
        partialInvLD (shiftRevTau w s) (fun k => x.getLsbD k.1) (fun k => z.getLsbD k.1) := by
      funext k; exact bitrevShiftOp_getLsbD w s x z k
    rw [hL, hR, hsub, hsub1, hsub2]
    exact congrFun (partialInvLD_left_distrib _ hτ _ _ _) ⟨i, hi⟩
  · intro x y
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hL := bitrevShiftOp_getLsbD w s (bitrevShiftOp w s x y) x ⟨i, hi⟩
    have hR := bitrevShiftOp_getLsbD w s x (bitrevShiftOp w s y x) ⟨i, hi⟩
    have hsub1 : (fun k : Fin w => (bitrevShiftOp w s x y).getLsbD k.1) =
        partialInvLD (shiftRevTau w s) (fun k => x.getLsbD k.1) (fun k => y.getLsbD k.1) := by
      funext k; exact bitrevShiftOp_getLsbD w s x y k
    have hsub2 : (fun k : Fin w => (bitrevShiftOp w s y x).getLsbD k.1) =
        partialInvLD (shiftRevTau w s) (fun k => y.getLsbD k.1) (fun k => x.getLsbD k.1) := by
      funext k; exact bitrevShiftOp_getLsbD w s y x k
    rw [hL, hR, hsub1, hsub2]
    exact congrFun (partialInvLD_flexible _ hτ _ _) ⟨i, hi⟩
  · intro hle
    let a : Fin w := ⟨s, by omega⟩
    let b : Fin w := ⟨w - 1, by omega⟩
    have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a, b] at this; omega
    have hτa : shiftRevTau w s a = some b := by
      unfold shiftRevTau; simp only [a, b, Nat.le_refl, ↓reduceDIte]
      congr 1; ext; dsimp only; omega
    have hτb : shiftRevTau w s b = some a := hτ a b hτa
    let xa : BitVec w := 1#w <<< s
    have hxa : ∀ k : Fin w, xa.getLsbD k.1 = decide (k = a) := fun k => by
      dsimp only [xa, a]
      rw [BitVec.getLsbD_shiftLeft]
      by_cases hks : k.1 = s
      · have h1 : k = ⟨s, by omega⟩ := Fin.ext hks
        have hlt : s < w := by omega
        have h1lt : 0 < w := by omega
        simp [h1, hlt, h1lt]
      · have hne : k ≠ ⟨s, by omega⟩ := fun h => hks (congrArg Fin.val h)
        by_cases hlt : k.1 < s
        · simp [hlt, hne]
        · have hbit : (1#w).getLsbD (k.1 - s) = false := by
            rw [BitVec.getLsbD_ofNat]
            have : (1 : Nat).testBit (k.1 - s) = false := by
              cases h : k.1 - s with
              | zero => omega
              | succ m => simp [Nat.testBit_succ]
            simp [this]
          simp [hlt, hbit, hne]
    have hx0 : ∀ k : Fin w, (0#w).getLsbD k.1 = false := fun k => by simp
    have hxab : xa.getLsbD b.1 = false := by rw [hxa b]; simp [hab.symm]
    have hxaa : xa.getLsbD a.1 = true := by rw [hxa a]; simp
    constructor
    · refine ⟨0#w, 0#w, xa, ?_⟩
      intro heq
      have hbit := congrArg (fun v : BitVec w => v.getLsbD a.1) heq
      rw [bitrevShiftOp_getLsbD, bitrevShiftOp_getLsbD] at hbit
      have hsub1 : (fun k : Fin w => (bitrevShiftOp w s 0#w 0#w).getLsbD k.1) =
          fun _ => false := by
        funext k; rw [bitrevShiftOp_getLsbD, partialInvLD_idemp]; simp
      have hsub2 : (fun k : Fin w => (bitrevShiftOp w s 0#w xa).getLsbD k.1) =
          partialInvLD (shiftRevTau w s) (fun _ => false) (fun k => xa.getLsbD k.1) := by
        funext k; rw [bitrevShiftOp_getLsbD]; simp
      rw [hsub1, hsub2] at hbit
      simp only [partialInvLD, hx0, hτa, hτb, hxab, hxaa] at hbit
      cases hbit
    · refine ⟨0#w, xa, ?_⟩
      intro heq
      have hbit := congrArg (fun v : BitVec w => v.getLsbD a.1) heq
      rw [bitrevShiftOp_getLsbD, bitrevShiftOp_getLsbD] at hbit
      simp only [partialInvLD, hx0, hτa, hxab, hxaa] at hbit
      cases hbit

/-! ## Part III: Non-Alexander Pure-Silicon Coset-Jump & XOR-Carry Both-Sided Knot Quandles -/

private theorem bv_comm_sub {w : Nat} (a b c : BitVec w) : (a + b) - c = (a - c) + b := by
  grind

private theorem bv_sub_add {w : Nat} (a b c : BitVec w) : a - (b + c) = (a - b) - c := by
  grind

private theorem bv_sub_sub {w : Nat} (a b c d : BitVec w) : (a + b) - (c + d) = ((a - c) + b) - d := by
  grind

private theorem cosetJump_add_mod {w k : Nat} (g : BitVec w → BitVec w)
    (hdiv : ∀ d : BitVec w, (g d).toNat % 2 ^ k = 0)
    (hmod : ∀ d₁ d₂ : BitVec w, d₁.toNat % 2 ^ k = d₂.toNat % 2 ^ k → g d₁ = g d₂)
    (a b : BitVec w) :
    g (a + g b) = g a ∧ g (a - g b) = g a := by
  by_cases hkw : k ≤ w
  · have hdvd : 2 ^ k ∣ 2 ^ w := Nat.pow_dvd_pow 2 hkw
    have hgb0 : (g b).toNat % 2 ^ k = 0 := hdiv b
    have hneg0 : (-g b).toNat % 2 ^ k = 0 := by
      rw [BitVec.toNat_neg]
      have hlt : (g b).toNat < 2 ^ w := (g b).isLt
      have h1 : (2 ^ w - (g b).toNat) % 2 ^ k = 0 := by
        rcases hdvd with ⟨q, hq⟩
        have hgbd : 2 ^ k ∣ (g b).toNat := Nat.dvd_of_mod_eq_zero hgb0
        rcases hgbd with ⟨r, hr⟩
        have hrq : r ≤ q := by
          have : 2 ^ k * r < 2 ^ k * q := by rw [← hr, ← hq]; exact hlt
          exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_left this)
        have hsub : 2 ^ w - (g b).toNat = 2 ^ k * (q - r) := by
          rw [hq, hr, Nat.mul_sub]
        rw [hsub]; exact Nat.mul_mod_right _ _
      exact (Nat.mod_mod_of_dvd _ hdvd).trans h1
    constructor
    · apply hmod
      rw [BitVec.toNat_add, Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod, hgb0, Nat.add_zero, Nat.mod_mod]
    · apply hmod
      rw [BitVec.sub_eq_add_neg, BitVec.toNat_add, Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod,
          hneg0, Nat.add_zero, Nat.mod_mod]
  · have hg_zero : ∀ d : BitVec w, g d = 0 := by
      intro d
      apply BitVec.eq_of_toNat_eq
      have hlt : (g d).toNat < 2 ^ k :=
        Nat.lt_trans (g d).isLt (Nat.pow_lt_pow_right (by omega) (by omega))
      have h0 := hdiv d
      rw [Nat.mod_eq_of_lt hlt] at h0
      simpa using h0
    simp [hg_zero]

theorem cosetJump_quandle_laws {w : Nat} (k : Nat) (g : BitVec w → BitVec w)
    (hg0 : g 0 = 0)
    (hdiv : ∀ d : BitVec w, (g d).toNat % 2 ^ k = 0)
    (hmod : ∀ d₁ d₂ : BitVec w, d₁.toNat % 2 ^ k = d₂.toNat % 2 ^ k → g d₁ = g d₂) :
    (∀ x : BitVec w, cosetJump g x x = x) ∧
    (∀ x y z : BitVec w,
      cosetJump g x (cosetJump g y z) = cosetJump g (cosetJump g x y) (cosetJump g x z)) ∧
    (∀ x y z : BitVec w,
      cosetJump g (cosetJump g x y) z = cosetJump g (cosetJump g x z) (cosetJump g y z)) ∧
    (∀ x y : BitVec w,
      cosetJump g (cosetJump g x y) x = cosetJump g x (cosetJump g y x)) ∧
    (∀ x y : BitVec w, cosetJumpInv g x (cosetJump g x y) = y) ∧
    (∀ x z : BitVec w, cosetJump g x (cosetJumpInv g x z) = z) := by
  have hadd : ∀ a b, g (a + g b) = g a := fun a b => (cosetJump_add_mod g hdiv hmod a b).1
  have hsub : ∀ a b, g (a - g b) = g a := fun a b => (cosetJump_add_mod g hdiv hmod a b).2
  have hg0' : g 0#w = 0#w := hg0
  have hgg : ∀ a, g (g a) = 0 := fun a => by
    have := hadd 0 a; rw [show (0 : BitVec w) + g a = g a by grind, hg0] at this; exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; simp [cosetJump, hg0']
  · intro x y z
    simp only [cosetJump]
    rw [bv_comm_sub z (g (z - y)) x, hadd (z - x) (z - y),
        bv_sub_sub z (g (z - x)) y (g (y - x)), hsub ((z - y) + g (z - x)) (y - x),
        hadd (z - y) (z - x)]
    grind
  · intro x y z
    simp only [cosetJump]
    rw [bv_sub_add z y (g (y - x)), hsub (z - y) (y - x),
        bv_sub_sub z (g (z - y)) z (g (z - x)), BitVec.sub_self, BitVec.zero_add,
        hsub (g (z - y)) (z - x), hgg (z - y)]
    grind
  · intro x y
    simp only [cosetJump]
    rw [bv_sub_add x y (g (y - x)), hsub (x - y) (y - x),
        bv_comm_sub x (g (x - y)) x, BitVec.sub_self, BitVec.zero_add, hgg (x - y)]
    grind
  · intro x y
    simp only [cosetJump, cosetJumpInv]
    rw [bv_comm_sub y (g (y - x)) x, hadd (y - x) (y - x)]
    grind
  · intro x z
    simp only [cosetJump, cosetJumpInv]
    rw [show (z - g (z - x)) - x = (z - x) - g (z - x) by grind, hsub (z - x) (z - x)]
    grind

private theorem nat_add_eq_xor_add_two_mul_and (a b : Nat) :
    a + b = (a ^^^ b) + 2 * (a &&& b) := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha0 : a = 0
    · subst ha0; simp
    · have hdiv_xor : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
        apply Nat.eq_of_testBit_eq; intro r
        rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_xor]
      have hdiv_and : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
        apply Nat.eq_of_testBit_eq; intro r
        rw [← Nat.testBit_succ, Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_and]
      have hmod_xor : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
        have hb := Nat.testBit_xor a b 0
        rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero] at hb
        rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
          rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2 <;>
          rcases Nat.mod_two_eq_zero_or_one (a ^^^ b) with h3 | h3 <;>
          simp [ha, hb2, h3] at hb ⊢
      have hmod_and : (a &&& b) % 2 = (a % 2) &&& (b % 2) := by
        have hb := Nat.testBit_and a b 0
        rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero] at hb
        rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
          rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2 <;>
          rcases Nat.mod_two_eq_zero_or_one (a &&& b) with h3 | h3 <;>
          simp [ha, hb2, h3] at hb ⊢
      have hih := ih (a / 2) (by omega) (b / 2)
      have hx_div : 2 * ((a / 2) ^^^ (b / 2)) + ((a % 2) ^^^ (b % 2)) = a ^^^ b := by
        rw [← hdiv_xor, ← hmod_xor]; exact Nat.div_add_mod (a ^^^ b) 2
      have ha_div : 2 * ((a / 2) &&& (b / 2)) + ((a % 2) &&& (b % 2)) = a &&& b := by
        rw [← hdiv_and, ← hmod_and]; exact Nat.div_add_mod (a &&& b) 2
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2 <;>
        (rw [ha, hb2] at hx_div ha_div;
         simp only [Nat.xor_zero, Nat.zero_xor, Nat.xor_self, Nat.and_zero, Nat.zero_and, Nat.and_self] at hx_div ha_div;
         omega)

private theorem bitVec_add_eq_xor_add_two_mul_and {w : Nat} (a b : BitVec w) :
    a + b = (a ^^^ b) + BitVec.ofNat w 2 * (a &&& b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_mul,
      BitVec.toNat_ofNat, BitVec.toNat_and, nat_add_eq_xor_add_two_mul_and]
  simp [Nat.add_mod, Nat.mul_mod]

private theorem bitVec_and_add_and_not {w : Nat} (a c : BitVec w) :
    (a &&& c) + (a &&& ~~~c) = a := by
  have hdisj : ((a &&& c).toNat &&& (a &&& ~~~c).toNat) = 0 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hr : r < w
    · rw [BitVec.testBit_toNat, BitVec.testBit_toNat]
      simp [hr]
      cases a[r] <;> cases c[r] <;> simp
    · rw [BitVec.testBit_toNat]
      have h0 : (a &&& c).getLsbD r = false := BitVec.getLsbD_of_ge _ r (by omega)
      simp [h0]
  have hor : (a &&& c) ||| (a &&& ~~~c) = a := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [hi]
    cases a[i] <;> cases c[i] <;> rfl
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, nat_add_eq_or_of_and_zero _ _ hdisj, ← BitVec.toNat_or, hor,
      Nat.mod_eq_of_lt a.isLt]

theorem xorCarryOp_eq_and_not (w : Nat) (c x y : BitVec w) :
    xorCarryOp w c x y =
      y - BitVec.ofNat w 2 * ((BitVec.ofNat w 2 * (y - x)) &&& ~~~c) := by
  unfold xorCarryOp
  let a : BitVec w := BitVec.ofNat w 2 * (y - x)
  have h1 : a + c = (a ^^^ c) + BitVec.ofNat w 2 * (a &&& c) :=
    bitVec_add_eq_xor_add_two_mul_and a c
  have h2 : (a &&& c) + (a &&& ~~~c) = a :=
    bitVec_and_add_and_not a c
  have h3 : BitVec.ofNat w 2 * x - y = y - a := by
    dsimp [a]; grind
  change (BitVec.ofNat w 2 * x - y) - (a ^^^ c) + c = y - BitVec.ofNat w 2 * (a &&& ~~~c)
  rw [h3]
  grind

theorem xorCarryQuandle_twoBitMask (w a : Nat) (ha : 1 ≤ a) (c : BitVec w)
    (hmask : ∀ r : Nat, 1 ≤ r → r + 1 < w → (~~~c).getLsbD r = true → r = a ∨ r = a + 1) :
    (∀ x : BitVec w, xorCarryOp w c x x = x) ∧
    (∀ x y z : BitVec w,
      xorCarryOp w c x (xorCarryOp w c y z) =
        xorCarryOp w c (xorCarryOp w c x y) (xorCarryOp w c x z)) ∧
    (∀ x y z : BitVec w,
      xorCarryOp w c (xorCarryOp w c x y) z =
        xorCarryOp w c (xorCarryOp w c x z) (xorCarryOp w c y z)) ∧
    (∀ x y : BitVec w,
      xorCarryOp w c (xorCarryOp w c x y) x =
        xorCarryOp w c x (xorCarryOp w c y x)) ∧
    (∃ inv : BitVec w → BitVec w → BitVec w,
      (∀ x y : BitVec w, inv x (xorCarryOp w c x y) = y) ∧
      (∀ x z : BitVec w, xorCarryOp w c x (inv x z) = z)) := by
  let g : BitVec w → BitVec w := fun d => -(BitVec.ofNat w 2 * ((BitVec.ofNat w 2 * d) &&& ~~~c))
  have hrew : ∀ x y : BitVec w, xorCarryOp w c x y = cosetJump g x y := by
    intro x y
    rw [xorCarryOp_eq_and_not]
    simp [cosetJump, g, BitVec.sub_eq_add_neg]
  have hg0 : g 0 = 0 := by simp [g]
  have hmul2 : ∀ u : BitVec w, BitVec.ofNat w 2 * u = u <<< 1 := by
    intro u
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft,
        Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm u.toNat 2,
        Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  have hpos_bits : ∀ d : BitVec w, ∀ r : Nat, r < w →
      ((BitVec.ofNat w 2 * ((BitVec.ofNat w 2 * d) &&& ~~~c))).getLsbD r = true →
      a + 1 ≤ r := by
    intro d r hr hbit
    rw [hmul2, BitVec.getLsbD_shiftLeft] at hbit
    simp only [hr, decide_true, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at hbit
    rcases hbit with ⟨hr1, hinner⟩
    rw [BitVec.getLsbD_and] at hinner
    simp only [Bool.and_eq_true] at hinner
    rcases hinner with ⟨h2d, hnc⟩
    rw [hmul2, BitVec.getLsbD_shiftLeft] at h2d
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h2d
    have hr_sub : 1 ≤ r - 1 := by omega
    have hr_lt : (r - 1) + 1 < w := by omega
    have hcase := hmask (r - 1) hr_sub hr_lt hnc
    omega
  have hdiv : ∀ d : BitVec w, (g d).toNat % 2 ^ (a + 1) = 0 := by
    intro d
    let u : BitVec w := BitVec.ofNat w 2 * ((BitVec.ofNat w 2 * d) &&& ~~~c)
    have hu_low : ∀ r < a + 1, u.toNat.testBit r = false := by
      intro r hr
      rw [BitVec.testBit_toNat]
      by_cases hrw : r < w
      · cases hu_r : u.getLsbD r
        · rfl
        · exfalso; have := hpos_bits d r hrw hu_r; omega
      · exact BitVec.getLsbD_of_ge u r (by omega)
    have hu_mod : u.toNat % 2 ^ (a + 1) = 0 := by
      apply Nat.eq_of_testBit_eq; intro r
      rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
      by_cases hr : r < a + 1
      · simp [hr, hu_low r hr]
      · simp [hr]
    change (-u).toNat % 2 ^ (a + 1) = 0
    by_cases hu0 : u.toNat = 0
    · have : u = 0 := BitVec.eq_of_toNat_eq hu0
      simp [this]
    · by_cases haw : a + 1 ≤ w
      · have hdvd : 2 ^ (a + 1) ∣ 2 ^ w := Nat.pow_dvd_pow 2 haw
        have hudvd : 2 ^ (a + 1) ∣ u.toNat := Nat.dvd_of_mod_eq_zero hu_mod
        rw [BitVec.toNat_neg]
        rcases hdvd with ⟨q, hq⟩
        rcases hudvd with ⟨r, hr⟩
        have hrq : r ≤ q := by
          have : 2 ^ (a + 1) * r < 2 ^ (a + 1) * q := by rw [← hr, ← hq]; exact u.isLt
          exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_left this)
        have hsub : 2 ^ w - u.toNat = 2 ^ (a + 1) * (q - r) := by rw [hq, hr, Nat.mul_sub]
        rw [Nat.mod_mod_of_dvd _ ⟨q, hq⟩, hsub]
        exact Nat.mul_mod_right _ _
      · have hlt : u.toNat < 2 ^ (a + 1) :=
          Nat.lt_trans u.isLt (Nat.pow_lt_pow_right (by omega) (by omega))
        rw [Nat.mod_eq_of_lt hlt] at hu_mod
        exact absurd hu_mod hu0
  have hmod : ∀ d₁ d₂ : BitVec w, d₁.toNat % 2 ^ (a + 1) = d₂.toNat % 2 ^ (a + 1) → g d₁ = g d₂ := by
    intro d₁ d₂ hEq
    dsimp only [g]
    congr 1
    apply BitVec.eq_of_getLsbD_eq; intro r hr
    simp only [hmul2, BitVec.getLsbD_shiftLeft]
    by_cases hr1 : r < 1
    · simp [hr1]
    · simp only [hr, hr1, decide_true, Bool.true_and, decide_false, Bool.not_false]
      rw [BitVec.getLsbD_and, BitVec.getLsbD_and]
      by_cases hnc : (~~~c).getLsbD (r - 1) = true
      · simp only [hnc, Bool.and_true]
        simp only [BitVec.getLsbD_shiftLeft]
        by_cases hr2 : r - 1 < 1
        · simp [hr2]
        · have hr_sub_ge : 1 ≤ r - 1 := by omega
          have hr_sub_lt : (r - 1) + 1 < w := by omega
          have hcase := hmask (r - 1) hr_sub_ge hr_sub_lt hnc
          have hbit_lt : r - 1 - 1 < a + 1 := by omega
          have hb_eq : d₁.getLsbD (r - 1 - 1) = d₂.getLsbD (r - 1 - 1) := by
            rw [← BitVec.testBit_toNat, ← BitVec.testBit_toNat]
            have h1 := congrArg (fun n => n.testBit (r - 1 - 1)) hEq
            rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow] at h1
            simpa [hbit_lt] using h1
          simp [hr2, hb_eq]
      · have hncf : (~~~c).getLsbD (r - 1) = false := Bool.eq_false_iff.mpr hnc
        simp [hncf]
  have hQ := cosetJump_quandle_laws (a + 1) g hg0 hdiv hmod
  simp only [hrew]
  exact ⟨hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2.1, ⟨cosetJumpInv g, hQ.2.2.2.2.1, hQ.2.2.2.2.2⟩⟩

theorem xorCarryQuandle_nonAlexander_nonInvolutive :
    (∀ x : BitVec 6, xorCarryOp 6 51#6 x x = x) ∧
    (∀ x y z : BitVec 6,
      xorCarryOp 6 51#6 x (xorCarryOp 6 51#6 y z) =
        xorCarryOp 6 51#6 (xorCarryOp 6 51#6 x y) (xorCarryOp 6 51#6 x z)) ∧
    (∀ x y z : BitVec 6,
      xorCarryOp 6 51#6 (xorCarryOp 6 51#6 x y) z =
        xorCarryOp 6 51#6 (xorCarryOp 6 51#6 x z) (xorCarryOp 6 51#6 y z)) ∧
    (∃ d₁ d₂ : BitVec 6,
      xorCarryOp 6 51#6 0 (d₁ + d₂) ≠ xorCarryOp 6 51#6 0 d₁ + xorCarryOp 6 51#6 0 d₂) ∧
    (∃ x y : BitVec 6, xorCarryOp 6 51#6 x (xorCarryOp 6 51#6 x y) ≠ y) := by
  have hmask : ∀ r : Nat, 1 ≤ r → r + 1 < 6 → (~~~51#6).getLsbD r = true → r = 2 ∨ r = 3 := by
    intro r hr1 hr2 hbit
    have hr_cases : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
    rcases hr_cases with rfl | rfl | rfl | rfl
    · simp at hbit
    · left; rfl
    · right; rfl
    · simp at hbit
  have hQ := xorCarryQuandle_twoBitMask 6 2 (by omega) 51#6 hmask
  refine ⟨hQ.1, hQ.2.1, hQ.2.2.1, ?_, ?_⟩
  · refine ⟨1#6, 1#6, ?_⟩; decide
  · refine ⟨0#6, 2#6, ?_⟩; decide

end SiliconLDQuandles
