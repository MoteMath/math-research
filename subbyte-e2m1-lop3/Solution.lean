/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubbyteE2M1Lop3

/-!
# Verified Solutions (`subbyte-e2m1-lop3`)
-/

namespace SubbyteE2M1Lop3Challenge

open SubbyteE2M1Lop3

theorem unpack_2t4b_to_e2m1_zero_lop3 (w0 w1 : Int)
    (hw0 : IsTrit w0) (hw1 : IsTrit w1) :
    let (n0, n1) := unpack2t4b (encode2t4b w0 w1)
    e2m1TwiceVal n0 = 2 * w0 ∧ e2m1TwiceVal n1 = 2 * w1 :=
  SubbyteE2M1Lop3.unpack_2t4b_to_e2m1_zero_lop3 w0 w1 hw0 hw1

theorem unpack_3t5b_to_e2m1_four_lop3 (w0 w1 w2 : Int)
    (hw0 : IsTrit w0) (hw1 : IsTrit w1) (hw2 : IsTrit w2) :
    let (n0, n1, n2) := unpack3t5b (encode3t5b w0 w1 w2)
    e2m1TwiceVal n0 = 2 * w0 ∧ e2m1TwiceVal n1 = 2 * w1 ∧ e2m1TwiceVal n2 = 2 * w2 :=
  SubbyteE2M1Lop3.unpack_3t5b_to_e2m1_four_lop3 w0 w1 w2 hw0 hw1 hw2

theorem unpack_3t5b_to_e2m1_three_gate_lower_bound
    (dec : BitVec 5 → BitVec 4 × BitVec 4 × BitVec 4)
    (hsurj : ∀ w0 w1 w2 : Int, IsTrit w0 → IsTrit w1 → IsTrit w2 →
      ∃ x : BitVec 5, decode3E2M1 (dec x) = (2 * w0, 2 * w1, 2 * w2)) :
    let f0 : BitVec 5 → Bool := fun x => e2m1TwiceVal (dec x).1 != 0
    let f1 : BitVec 5 → Bool := fun x => e2m1TwiceVal (dec x).2.1 != 0
    let f2 : BitVec 5 → Bool := fun x => e2m1TwiceVal (dec x).2.2 != 0
    (18 ≤ weight f0 ∧ weight f0 ≤ 23) ∧
    (18 ≤ weight f1 ∧ weight f1 ≤ 23) ∧
    (18 ≤ weight f2 ∧ weight f2 ≤ 23) ∧
    (∀ g : BitVec 5 → Bool, DependsOnAtMost2 g → weight g % 8 = 0) ∧
    (¬ DependsOnAtMost2 f0 ∧ ¬ DependsOnAtMost2 f1 ∧ ¬ DependsOnAtMost2 f2) ∧
    (f0 ≠ f1 ∧ f0 ≠ f2 ∧ f1 ≠ f2) :=
  SubbyteE2M1Lop3.unpack_3t5b_to_e2m1_three_gate_lower_bound dec hsurj

theorem quinary_3w7b_five_var_impossibility
    (dec : BitVec 7 → Fin 5 × Fin 5 × Fin 5)
    (hsurj : ∀ q0 q1 q2 : Fin 5, ∃ x : BitVec 7, dec x = (q0, q1, q2)) :
    (∀ (s : Fin 3) (P : Fin 5 → Bool),
      1 ≤ countFin5 P → countFin5 P ≤ 4 →
      let k := countFin5 P
      let f : BitVec 7 → Bool := fun x => P (slot3 s (dec x))
      25 * k ≤ weight f ∧ weight f ≤ 25 * k + 3 ∧ weight f % 8 ≠ 0) ∧
    (∀ g : BitVec 7 → Bool, DependsOnAtMost4 g → weight g % 8 = 0) ∧
    (∀ (s : Fin 3) (P : Fin 5 → Bool),
      1 ≤ countFin5 P → countFin5 P ≤ 4 →
      ¬ DependsOnAtMost4 (fun x => P (slot3 s (dec x)))) :=
  SubbyteE2M1Lop3.quinary_3w7b_five_var_impossibility dec hsurj

theorem asymmetric_2bit_polarity_flip_exact :
    (asym2Val false false = 0) ∧
    (∀ b1 b0 b1' b0' : Bool, asym2Val b1 b0 = asym2Val b1' b0' → b1 = b1' ∧ b0 = b0') ∧
    (∀ v : Int, (v = -2 ∨ v = -1 ∨ v = 0 ∨ v = 1) ↔ ∃ b1 b0 : Bool, asym2Val b1 b0 = v) ∧
    (∀ v : Int, (v = -1 ∨ v = 0 ∨ v = 1 ∨ v = 2) ↔ ∃ b1 b0 : Bool, -asym2Val b1 b0 = v) ∧
    (∀ xs : List (Bool × Bool × Int),
      xs.foldl (fun acc (b1, b0, a) => acc + asym2Val b1 b0 * a) 0 =
      xs.foldl (fun acc (_, b0, a) => acc + (if b0 then a else 0)) 0 -
      2 * xs.foldl (fun acc (b1, _, a) => acc + (if b1 then a else 0)) 0) :=
  SubbyteE2M1Lop3.asymmetric_2bit_polarity_flip_exact

theorem compressor_4to2_lop3_depth_inversion :
    (∀ i j k : Fin 5, ∀ imm : UInt8,
      ∃ v : Fin 5 → Bool,
        lop3 imm (v i) (v j) (v k) ≠ sum4to2 (v 0) (v 1) (v 2) (v 3) (v 4)) ∧
    (∀ a b c : Bool,
      (if sum3to2 a b c then (1 : Nat) else 0) + 2 * (if carry3to2 a b c then 1 else 0) =
      (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)) :=
  SubbyteE2M1Lop3.compressor_4to2_lop3_depth_inversion

end SubbyteE2M1Lop3Challenge
