/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TernaryLop3Kulisch

/-!
# Verified Solutions (`ternary-lop3-kulisch`)
-/

namespace TernaryLop3KulischChallenge

open TernaryLop3Kulisch

theorem ternary_k2_4_lop3_exact_and_lb :
    (∀ p0 n0 p1 n1 : Bool,
      tritValid p0 n0 = true → tritValid p1 n1 = true →
      let (s0, s1, s2) := ternaryK2Lop3 p0 n0 p1 n1
      twosComp3 s0 s1 s2 = tritVal p0 n0 + tritVal p1 n1) ∧
    (ternaryK2Dag.length = 4 ∧
      ∀ x : Fin 4 → Bool, validK2 x →
        twosComp3 (evalWire ternaryK2Dag x 5) (evalWire ternaryK2Dag x 7) (evalWire ternaryK2Dag x 6) =
          tritVal (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) +
          tritVal (x ⟨2, by decide⟩) (x ⟨3, by decide⟩)) ∧
    (∀ (dag : Lop3Dag) (o0 o1 o2 : Nat),
      (∀ x : Fin 4 → Bool, validK2 x →
        twosComp3 (evalWire dag x o0) (evalWire dag x o1) (evalWire dag x o2) =
          tritVal (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) +
          tritVal (x ⟨2, by decide⟩) (x ⟨3, by decide⟩)) →
      4 ≤ dag.length) :=
  TernaryLop3Kulisch.ternary_k2_4_lop3_exact_and_lb

theorem ternary_k3_7_lop3_exact :
    (∀ p0 n0 p1 n1 p2 n2 : Bool,
      tritValid p0 n0 = true → tritValid p1 n1 = true → tritValid p2 n2 = true →
      let (s0, s1, s2) := ternaryK3Lop3 p0 n0 p1 n1 p2 n2
      twosComp3 s0 s1 s2 = tritVal p0 n0 + tritVal p1 n1 + tritVal p2 n2) ∧
    (ternaryK3Dag.length = 7 ∧
      ∀ x : Fin 6 → Bool, validK3 x →
        twosComp3 (evalWire ternaryK3Dag x 8) (evalWire ternaryK3Dag x 11) (evalWire ternaryK3Dag x 12) =
          tritVal (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) +
          tritVal (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) +
          tritVal (x ⟨4, by decide⟩) (x ⟨5, by decide⟩)) ∧
    (∀ (dag : Lop3Dag) (o0 o1 o2 : Nat),
      (∀ x : Fin 6 → Bool, validK3 x →
        twosComp3 (evalWire dag x o0) (evalWire dag x o1) (evalWire dag x o2) =
          tritVal (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) +
          tritVal (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) +
          tritVal (x ⟨4, by decide⟩) (x ⟨5, by decide⟩)) →
      5 ≤ dag.length) :=
  TernaryLop3Kulisch.ternary_k3_7_lop3_exact

theorem harley_seal_n7_8_lop3_exact_and_lb :
    (∀ x0 x1 x2 x3 x4 x5 x6 : Bool,
      let (s0, s1, s2) := harleySealN7Lop3 x0 x1 x2 x3 x4 x5 x6
      u3Val s0 s1 s2 = popcount7 x0 x1 x2 x3 x4 x5 x6) ∧
    (harleySealN7Dag.length = 8 ∧
      ∀ x : Fin 7 → Bool,
        u3Val (evalWire harleySealN7Dag x 11) (evalWire harleySealN7Dag x 13) (evalWire harleySealN7Dag x 14) =
          popcount7Vec x) ∧
    (∀ (dag : Lop3Dag) (o0 o1 o2 : Nat),
      (∀ x : Fin 7 → Bool,
        u3Val (evalWire dag x o0) (evalWire dag x o1) (evalWire dag x o2) = popcount7Vec x) →
      5 ≤ dag.length) :=
  TernaryLop3Kulisch.harley_seal_n7_8_lop3_exact_and_lb

theorem fp8_e4m3_exact_kulisch_49bit_int64_theorem :
    (∀ x y : BitVec 8, e4m3Finite x = true → e4m3Finite y = true →
      (e4m3ProdScaled x y).natAbs ≤ 52613349376 ∧ (e4m3ProdScaled x y).natAbs < 2 ^ 36) ∧
    (e4m3Finite (BitVec.ofNat 8 0x7E) = true ∧
      e4m3ProdScaled (BitVec.ofNat 8 0x7E) (BitVec.ofNat 8 0x7E) = 52613349376) ∧
    (∀ pairs : List (BitVec 8 × BitVec 8),
      (∀ p ∈ pairs, e4m3Finite p.1 = true ∧ e4m3Finite p.2 = true) →
      (e4m3DotScaled pairs).natAbs ≤ pairs.length * 52613349376) ∧
    (∀ pairs : List (BitVec 8 × BitVec 8),
      (∀ p ∈ pairs, e4m3Finite p.1 = true ∧ e4m3Finite p.2 = true) →
      pairs.length ≤ 175304787 →
      (e4m3DotScaled pairs).natAbs < 2 ^ 63) ∧
    (175304788 * 52613349376 ≥ 2 ^ 63) ∧
    (∀ pairs : List (BitVec 8 × BitVec 8),
      (∀ p ∈ pairs, e4m3Finite p.1 = true ∧ e4m3Finite p.2 = true) →
      pairs.length ≤ 4096 →
      (e4m3DotScaled pairs).natAbs < 2 ^ 48) ∧
    (2 ^ 47 ≤ 4096 * 52613349376 ∧ 4096 * 52613349376 < 2 ^ 48) :=
  TernaryLop3Kulisch.fp8_e4m3_exact_kulisch_49bit_int64_theorem

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
  TernaryLop3Kulisch.swar64_ternary_int2_dot_zero_overflow

theorem fp8_e5m2_vs_e4m3_kulisch_width_gap :
    (∀ x y : BitVec 8, e5m2Finite x = true → e5m2Finite y = true →
      (e5m2ProdScaled x y).natAbs ≤ 14123288431433875456) ∧
    (e5m2Finite (BitVec.ofNat 8 0x7B) = true ∧
      e5m2ProdScaled (BitVec.ofNat 8 0x7B) (BitVec.ofNat 8 0x7B) = 14123288431433875456 ∧
      2 ^ 63 ≤ (e5m2ProdScaled (BitVec.ofNat 8 0x7B) (BitVec.ofNat 8 0x7B)).natAbs ∧
      (e5m2ProdScaled (BitVec.ofNat 8 0x7B) (BitVec.ofNat 8 0x7B)).natAbs < 2 ^ 64) ∧
    (2 ^ 35 ≤ 52613349376 ∧ 52613349376 < 2 ^ 36) ∧
    (2 ^ 47 ≤ 4096 * 52613349376 ∧ 4096 * 52613349376 < 2 ^ 48) ∧
    (2 ^ 75 ≤ 4096 * 14123288431433875456 ∧ 4096 * 14123288431433875456 < 2 ^ 76) :=
  TernaryLop3Kulisch.fp8_e5m2_vs_e4m3_kulisch_width_gap

end TernaryLop3KulischChallenge
