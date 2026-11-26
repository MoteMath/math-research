/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Fp8E4m3Lop3.Dyadic

/-!
# Exact 28-`LOP3` Zero-FP `FP8-E4M3FN × FP4-E2M1` Aligned Product (`E4m3E2m1Mul.lean`)

Kernel-checked proof of `fp8_e4m3_times_e2m1_28_lop3_exact`:
- `1` `LOP3` sign XOR (`0x3C`) + `3` `LOP3` implicit-bit flags (`0xFE`, `0xFC`, `0xFC`) +
  `14` `LOP3` 4-bit × 2-bit significand product `P[5:0] = s_a * s_b` (64/64 exact) +
  `10` `LOP3` 5-bit aligned exponent sum `E_sum[4:0] = max(e_a, 1) + max(e_b, 1) - 1` (64/64 exact)
  = `28` `LOP3` gates total (`0.875` `LOP3`/elem at 32-wide bit-sliced).
- Proves exact sign, significand product, and aligned exponent for all `256 × 16 = 4,096` pairs,
  and the exact integer dyadic product law
  `alignedProdScaled1024 (e4m3TimesE2m1Aligned28 a b) = e4m3ScaledVal a * e2m1TwiceVal b`
  for all `4,096` pairs `(a, b)`.
-/

namespace Fp8E4m3Lop3

set_option maxRecDepth 16384

private theorem sig_prod_64_check :
    checkBv6 (fun x =>
      (evalLop3Dag6 e4m3E2m1SigProdDag x).toNat == (x.toNat &&& 0xF) * ((x.toNat >>> 4) &&& 0x3)) = true := by
  decide

private theorem exp_sum_64_check :
    checkBv6 (fun x =>
      (evalLop3Dag5 e4m3E2m1ExpSumDag x).toNat ==
        max (x.toNat &&& 0xF) 1 + max ((x.toNat >>> 4) &&& 0x3) 1 - 1) = true := by
  decide

private theorem e4m3_mag_factor_check :
    checkBv8 (fun a =>
      e4m3MagScaled a == e4m3Sig a * (2 ^ (max (e4m3ExpField a) 1 - 1))) = true := by
  decide

private theorem e2m1_mag_factor_check :
    checkBv4 (fun b =>
      e2m1MagVal (b.truncate 3) == e2m1Sig b * (2 ^ (max (e2m1ExpField b) 1 - 1))) = true := by
  decide

private theorem e4m3_sig_bits_check :
    checkBv8 (fun a =>
      ((a.toNat &&& 0x7) ||| (if e4m3EaNzLop3 a then 8 else 0)) == e4m3Sig a) = true := by
  decide

private theorem e2m1_sig_bits_check :
    checkBv4 (fun b =>
      ((b.toNat &&& 0x1) ||| (if e2m1EbNzLop3 b then 2 else 0)) == e2m1Sig b) = true := by
  decide

private theorem e4m3_sig_lt16 : ∀ a : BitVec 8, e4m3Sig a < 16 := by
  have hcheck : checkBv8 (fun a => decide (e4m3Sig a < 16)) = true := by decide
  intro a
  exact of_decide_eq_true (forall_bv8_of_checkBv8 hcheck a)

private theorem e2m1_sig_lt4 : ∀ b : BitVec 4, e2m1Sig b < 4 := by
  have hcheck : checkBv4 (fun b => decide (e2m1Sig b < 4)) = true := by decide
  intro b
  exact of_decide_eq_true (forall_bv4_of_checkBv4 hcheck b)

private theorem e4m3_exp_lt16 : ∀ a : BitVec 8, e4m3ExpField a < 16 := by
  have hcheck : checkBv8 (fun a => decide (e4m3ExpField a < 16)) = true := by decide
  intro a
  exact of_decide_eq_true (forall_bv8_of_checkBv8 hcheck a)

private theorem e2m1_exp_lt4 : ∀ b : BitVec 4, e2m1ExpField b < 4 := by
  have hcheck : checkBv4 (fun b => decide (e2m1ExpField b < 4)) = true := by decide
  intro b
  exact of_decide_eq_true (forall_bv4_of_checkBv4 hcheck b)

private theorem pack6_split (x y : Nat) (hx : x < 16) (hy : y < 4) :
    let v := BitVec.ofNat 6 (x ||| (y <<< 4))
    (v.toNat &&& 0xF) = x ∧ ((v.toNat >>> 4) &&& 0x3) = y := by
  have hcheck : checkPow2 (fun k =>
      let xx := k % 16
      let yy := k / 16
      let v := BitVec.ofNat 6 (xx ||| (yy <<< 4))
      decide ((v.toNat &&& 0xF) = xx ∧ ((v.toNat >>> 4) &&& 0x3) = yy)) 6 0 = true := by decide
  have hk : x + 16 * y < 64 := by omega
  have h := checkPow2_spec _ 6 0 hcheck (x + 16 * y) (Nat.zero_le _) hk
  have hmod : (x + 16 * y) % 16 = x := by omega
  have hdiv : (x + 16 * y) / 16 = y := by omega
  simp only [hmod, hdiv, decide_eq_true_eq] at h
  exact h

private theorem e2m1_sig_shift_check :
    checkBv4 (fun b =>
      (((b.toNat &&& 0x1) <<< 4) ||| (if e2m1EbNzLop3 b then 32 else 0)) ==
        (e2m1Sig b <<< 4)) = true := by
  decide

private theorem sigIn_eq (a : BitVec 8) (b : BitVec 4) :
    let sigIn : BitVec 6 := BitVec.ofNat 6 (
      (a.toNat &&& 0x7) |||
      (if e4m3EaNzLop3 a then 8 else 0) |||
      ((b.toNat &&& 0x1) <<< 4) |||
      (if e2m1EbNzLop3 b then 32 else 0))
    sigIn = BitVec.ofNat 6 (e4m3Sig a ||| (e2m1Sig b <<< 4)) := by
  have ha := beq_iff_eq.mp (forall_bv8_of_checkBv8 e4m3_sig_bits_check a)
  have hb := beq_iff_eq.mp (forall_bv4_of_checkBv4 e2m1_sig_shift_check b)
  dsimp only
  rw [Nat.or_assoc, ha, hb]

private theorem sign_lop3_eq (a : BitVec 8) (b : BitVec 4) :
    e4m3E2m1SignLop3 a b = (a.getLsbD 7 != b.getLsbD 3) := by
  unfold e4m3E2m1SignLop3 lop3
  cases a.getLsbD 7 <;> cases b.getLsbD 3 <;> decide

private theorem signed_mul_int (sa sb : Bool) (ma mb : Nat) :
    (if sa != sb then -((ma * mb : Nat) : Int) else ((ma * mb : Nat) : Int)) =
      (if sa then -(ma : Int) else (ma : Int)) * (if sb then -(mb : Int) else (mb : Int)) := by
  cases sa <;> cases sb <;> simp [Int.neg_mul, Int.mul_neg, Int.neg_neg]

/-- Theorem 4 (Frontier 3): Exact 28-`LOP3` zero-FP `FP8-E4M3FN × FP4-E2M1` aligned product. -/
theorem fp8_e4m3_times_e2m1_28_lop3_exact :
    e4m3TimesE2m1GateCount = 28 ∧
    e4m3E2m1SigProdDag.gates.length = 14 ∧
    e4m3E2m1ExpSumDag.gates.length = 10 ∧
    (∀ x : BitVec 6,
      (evalLop3Dag6 e4m3E2m1SigProdDag x).toNat = (x.toNat &&& 0xF) * ((x.toNat >>> 4) &&& 0x3)) ∧
    (∀ x : BitVec 6,
      (evalLop3Dag5 e4m3E2m1ExpSumDag x).toNat =
        max (x.toNat &&& 0xF) 1 + max ((x.toNat >>> 4) &&& 0x3) 1 - 1) ∧
    (∀ a : BitVec 8, ∀ b : BitVec 4,
      let r := e4m3TimesE2m1Aligned28 a b
      r.1 = (a.getLsbD 7 != b.getLsbD 3) ∧
      r.2.1.toNat = e4m3Sig a * e2m1Sig b ∧
      r.2.2.toNat = max (e4m3ExpField a) 1 + max (e2m1ExpField b) 1 - 1 ∧
      alignedProdScaled1024 r = e4m3ScaledVal a * e2m1TwiceVal b) := by
  have hsig64 : ∀ x : BitVec 6,
      (evalLop3Dag6 e4m3E2m1SigProdDag x).toNat = (x.toNat &&& 0xF) * ((x.toNat >>> 4) &&& 0x3) := by
    intro x
    exact beq_iff_eq.mp (forall_bv6_of_checkBv6 sig_prod_64_check x)
  have hexp64 : ∀ x : BitVec 6,
      (evalLop3Dag5 e4m3E2m1ExpSumDag x).toNat =
        max (x.toNat &&& 0xF) 1 + max ((x.toNat >>> 4) &&& 0x3) 1 - 1 := by
    intro x
    exact beq_iff_eq.mp (forall_bv6_of_checkBv6 exp_sum_64_check x)
  refine ⟨by decide, by decide, by decide, hsig64, hexp64, ?_⟩
  intro a b
  have hsgn : (e4m3TimesE2m1Aligned28 a b).1 = (a.getLsbD 7 != b.getLsbD 3) := sign_lop3_eq a b
  have hp : (e4m3TimesE2m1Aligned28 a b).2.1.toNat = e4m3Sig a * e2m1Sig b := by
    dsimp only [e4m3TimesE2m1Aligned28]
    rw [sigIn_eq a b, hsig64]
    have hsp := pack6_split (e4m3Sig a) (e2m1Sig b) (e4m3_sig_lt16 a) (e2m1_sig_lt4 b)
    rw [hsp.1, hsp.2]
  have he : (e4m3TimesE2m1Aligned28 a b).2.2.toNat =
      max (e4m3ExpField a) 1 + max (e2m1ExpField b) 1 - 1 := by
    dsimp only [e4m3TimesE2m1Aligned28]
    change (evalLop3Dag5 e4m3E2m1ExpSumDag
      (BitVec.ofNat 6 (e4m3ExpField a ||| (e2m1ExpField b <<< 4)))).toNat = _
    rw [hexp64]
    have hsp := pack6_split (e4m3ExpField a) (e2m1ExpField b) (e4m3_exp_lt16 a) (e2m1_exp_lt4 b)
    rw [hsp.1, hsp.2]
  refine ⟨hsgn, hp, he, ?_⟩
  dsimp only [alignedProdScaled1024, e4m3ScaledVal, e2m1TwiceVal]
  rw [hsgn, hp, he]
  have hma := beq_iff_eq.mp (forall_bv8_of_checkBv8 e4m3_mag_factor_check a)
  have hmb := beq_iff_eq.mp (forall_bv4_of_checkBv4 e2m1_mag_factor_check b)
  rw [hma, hmb]
  have hexpArith :
      max (e4m3ExpField a) 1 + max (e2m1ExpField b) 1 - 1 - 1 =
      (max (e4m3ExpField a) 1 - 1) + (max (e2m1ExpField b) 1 - 1) := by
    have h1 : 1 ≤ max (e4m3ExpField a) 1 := Nat.le_max_right _ _
    have h2 : 1 ≤ max (e2m1ExpField b) 1 := Nat.le_max_right _ _
    omega
  have hmagEq :
      (e4m3Sig a * e2m1Sig b) <<< (max (e4m3ExpField a) 1 + max (e2m1ExpField b) 1 - 1 - 1) =
      (e4m3Sig a * 2 ^ (max (e4m3ExpField a) 1 - 1)) *
      (e2m1Sig b * 2 ^ (max (e2m1ExpField b) 1 - 1)) := by
    rw [Nat.shiftLeft_eq, hexpArith, Nat.pow_add]
    have h1 : e4m3Sig a * e2m1Sig b * (2 ^ (max (e4m3ExpField a) 1 - 1) * 2 ^ (max (e2m1ExpField b) 1 - 1)) =
        e4m3Sig a * (e2m1Sig b * 2 ^ (max (e4m3ExpField a) 1 - 1)) * 2 ^ (max (e2m1ExpField b) 1 - 1) := by
      simp [Nat.mul_assoc]
    rw [h1, Nat.mul_comm (e2m1Sig b) (2 ^ (max (e4m3ExpField a) 1 - 1))]
    simp [Nat.mul_assoc]
  rw [hmagEq]
  exact signed_mul_int (a.getLsbD 7) (b.getLsbD 3) _ _

end Fp8E4m3Lop3
