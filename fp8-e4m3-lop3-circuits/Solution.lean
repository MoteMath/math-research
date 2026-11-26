/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Fp8E4m3Lop3

/-!
# Verified Solutions (`fp8-e4m3-lop3-circuits`)
-/

namespace Fp8E4m3Lop3Challenge

open Fp8E4m3Lop3

theorem fp8_e4m3_rsqrt_15_lop3_exact :
    e4m3RsqrtPosDag.gates.length = 15 ∧
    dagDepth e4m3RsqrtPosDag = 8 ∧
    (∀ x : BitVec 8, isPosFiniteE4M3 x = true →
      isExactRneRsqrtE4M3 x (evalLop3Dag8 e4m3RsqrtPosDag x) = true) ∧
    (∀ x : BitVec 8, isPosFiniteE4M3 x = true →
      (evalLop3Dag8 e4m3RsqrtPosDag x).getLsbD 7 = false) :=
  Fp8E4m3Lop3.fp8_e4m3_rsqrt_15_lop3_exact

theorem fp8_e4m3_rsqrt_full_33_lop3_exact :
    e4m3RsqrtFullDag.gates.length = 33 ∧
    dagDepth e4m3RsqrtFullDag = 14 ∧
    (∀ x : BitVec 8, isPosFiniteE4M3 x = true →
      evalLop3Dag8 e4m3RsqrtFullDag x = evalLop3Dag8 e4m3RsqrtPosDag x ∧
      isExactRneRsqrtE4M3 x (evalLop3Dag8 e4m3RsqrtFullDag x) = true) ∧
    (∀ x : BitVec 8, isPosFiniteE4M3 x = false →
      evalLop3Dag8 e4m3RsqrtFullDag x = 0x7F#8) :=
  Fp8E4m3Lop3.fp8_e4m3_rsqrt_full_33_lop3_exact

theorem fp8_e4m3_activations_lop3_exact :
    e4m3ExpDag.gates.length = 67 ∧
    dagDepth e4m3ExpDag = 9 ∧
    (∀ x : BitVec 8, isFiniteE4M3 x = true →
      evalLop3Dag8 e4m3ExpDag x = e4m3ExpRefTable.getD x.toNat 0#8) ∧
    e4m3GeluDag.gates.length = 82 ∧
    dagDepth e4m3GeluDag = 15 ∧
    (∀ x : BitVec 8, isFiniteE4M3 x = true →
      evalLop3Dag8 e4m3GeluDag x = e4m3GeluRefTable.getD x.toNat 0#8) ∧
    (∀ x : BitVec 8, isFiniteE4M3 x = true →
      (evalLop3Dag8 e4m3GeluDag x).getLsbD 6 =
        lop3 0x04#8 (x.getLsbD 7) (x.getLsbD 6) (x.getLsbD 7)) ∧
    e4m3SiluDag.gates.length = 93 ∧
    dagDepth e4m3SiluDag = 16 ∧
    (∀ x : BitVec 8, isFiniteE4M3 x = true →
      evalLop3Dag8 e4m3SiluDag x = e4m3SiluRefTable.getD x.toNat 0#8) ∧
    (∀ x : BitVec 8, isFiniteE4M3 x = true →
      (evalLop3Dag8 e4m3SiluDag x).getLsbD 7 = x.getLsbD 7) :=
  Fp8E4m3Lop3.fp8_e4m3_activations_lop3_exact

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
      alignedProdScaled1024 r = e4m3ScaledVal a * e2m1TwiceVal b) :=
  Fp8E4m3Lop3.fp8_e4m3_times_e2m1_28_lop3_exact

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
    essentialVarCountOn isFiniteE4M3 (outBit8 (evalLop3Dag8 e4m3SiluDag) 7) = 1 :=
  Fp8E4m3Lop3.fp8_e4m3_lop3_fanin_lower_bound

theorem fp8_e4m3_exact_dyadic_value_law :
    e4m3ScaledVal 0x7E#8 = 448 * 512 ∧
    e4m3ScaledVal 0x01#8 = 1 ∧
    (∀ x : BitVec 8, isFiniteE4M3 x = true →
      -(448 * 512) ≤ e4m3ScaledVal x ∧ e4m3ScaledVal x ≤ 448 * 512) ∧
    (∀ x : BitVec 8, isPosFiniteE4M3 x = true → 1 ≤ e4m3ScaledVal x) ∧
    (∀ x : BitVec 8, isFiniteE4M3 x = true →
      e4m3ScaledVal (x ^^^ 0x80#8) = -e4m3ScaledVal x) ∧
    (∀ x y : BitVec 8, isPosFiniteE4M3 x = true → isPosFiniteE4M3 y = true →
      x.toNat < y.toNat → e4m3ScaledVal x < e4m3ScaledVal y) ∧
    (∀ x : BitVec 8, isFiniteE4M3 x = true →
      (e4m3ScaledVal x = 0 ↔ isZeroE4M3 x = true)) ∧
    countBv8 isPosFiniteE4M3 = 126 ∧
    countBv8 isNegFiniteE4M3 = 126 ∧
    countBv8 isZeroE4M3 = 2 ∧
    countBv8 isNanE4M3 = 2 :=
  Fp8E4m3Lop3.fp8_e4m3_exact_dyadic_value_law

end Fp8E4m3Lop3Challenge
