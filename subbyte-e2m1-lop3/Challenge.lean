/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubbyteE2M1Lop3.Defs

/-!
# Trusted Challenge Statements (`subbyte-e2m1-lop3`)

Statements of the six headline theorems for Cluster 10 sub-byte `LOP3` circuits:
1. `unpack_2t4b_to_e2m1_zero_lop3`: Exact 0-`LOP3` 2-trit / 4-bit → E2M1 unpacker (9/9 pairs).
2. `unpack_3t5b_to_e2m1_four_lop3`: Exact 4-`LOP3` 3-trit / 5-bit → E2M1 unpacker (27/27 triples).
3. `unpack_3t5b_to_e2m1_three_gate_lower_bound`: General ≥3-`LOP3` lower bound for any surjective 3-trit / 5-bit → E2M1 decoder.
4. `quinary_3w7b_five_var_impossibility`: General ≥5-variable support barrier (`LOP3` depth ≥ 2) for any surjective 3-quinary / 7-bit decoder.
5. `asymmetric_2bit_polarity_flip_exact`: Bijective 2-bit asymmetric `{-2, -1, 0, +1}` ↔ `{-1, 0, +1, +2}` duality and exact 2-plane dot product identity.
6. `compressor_4to2_lop3_depth_inversion`: 4:2 compressor 5-input parity requires `LOP3` depth ≥ 2, while 3:2 CSA is exact in 2 `LOP3` gates at depth 1.
-/

namespace SubbyteE2M1Lop3Challenge

open SubbyteE2M1Lop3

/-- Theorem 1 (`I093` 2t4b): The 0-`LOP3` pure bit-wire unpacker `unpack2t4b` and encoder
    `encode2t4b` decode every ternary pair `(w0, w1) ∈ {-1, 0, +1}^2` to exact E2M1 nibbles
    `(2 * w0, 2 * w1)`. -/
theorem unpack_2t4b_to_e2m1_zero_lop3 (w0 w1 : Int)
    (hw0 : IsTrit w0) (hw1 : IsTrit w1) :
    let (n0, n1) := unpack2t4b (encode2t4b w0 w1)
    e2m1TwiceVal n0 = 2 * w0 ∧ e2m1TwiceVal n1 = 2 * w1 := by
  sorry

/-- Theorem 2 (`I093` 3t5b): The exact 4-`LOP3` unpacker `unpack3t5b` and encoder
    `encode3t5b` decode every ternary triple `(w0, w1, w2) ∈ {-1, 0, +1}^3` to exact E2M1 nibbles
    `(2 * w0, 2 * w1, 2 * w2)` (27/27 triples exact, `-58.33%` VRAM vs FP4). -/
theorem unpack_3t5b_to_e2m1_four_lop3 (w0 w1 w2 : Int)
    (hw0 : IsTrit w0) (hw1 : IsTrit w1) (hw2 : IsTrit w2) :
    let (n0, n1, n2) := unpack3t5b (encode3t5b w0 w1 w2)
    e2m1TwiceVal n0 = 2 * w0 ∧ e2m1TwiceVal n1 = 2 * w1 ∧ e2m1TwiceVal n2 = 2 * w2 := by
  sorry

/-- Theorem 3 (`I093` lower bound): For ANY surjective 3-trit / 5-bit → E2M1 decoder
    `dec : BitVec 5 → BitVec 4 × BitVec 4 × BitVec 4`:
    - every nonzero-magnitude indicator `f_i(x) := (e2m1TwiceVal (dec x)_i != 0)` has Hamming
      weight in `[18, 23]`,
    - every Boolean function on `BitVec 5` depending on `≤ 2` input bits has `weight g % 8 = 0`,
    - therefore no `f_i` depends on `≤ 2` input bits (each requires `≥ 3` essential variables),
      and `f_0, f_1, f_2` are pairwise distinct, forcing `≥ 3` distinct `LOP3` gates. -/
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
    (f0 ≠ f1 ∧ f0 ≠ f2 ∧ f1 ≠ f2) := by
  sorry

/-- Theorem 4 (`I100`/`I091` quinary barrier): For ANY surjective 3-quinary / 7-bit decoder
    `dec : BitVec 7 → Fin 5 × Fin 5 × Fin 5`:
    - for any slot `s : Fin 3` and any non-constant predicate `P : Fin 5 → Bool`
      (`1 ≤ countFin5 P ≤ 4`), the output bit `f(x) := P (slot3 s (dec x))` has weight
      `25 * k ≤ weight f ≤ 25 * k + 3` (`k = countFin5 P`), hence `weight f % 8 ≠ 0`,
    - every Boolean function on `BitVec 7` depending on `≤ 4` input bits has `weight g % 8 = 0`,
    - therefore no non-trivial output bit can depend on `≤ 4` input bits (`LOP3` depth `≥ 2`). -/
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
      ¬ DependsOnAtMost4 (fun x => P (slot3 s (dec x)))) := by
  sorry

/-- Theorem 5 (`I098`/`I100` asymmetric 2-bit codebook):
    `asym2Val (b1 b0) = -2*b1 + b0` is an exact bijection onto `{-2, -1, 0, +1}` with exact zero
    `(false, false) ↦ 0`, its negation `-asym2Val` is an exact bijection onto `{-1, 0, +1, +2}`
    (free polarity flip via scale sign), and the 2-plane dot product identity holds for all lists. -/
theorem asymmetric_2bit_polarity_flip_exact :
    (asym2Val false false = 0) ∧
    (∀ b1 b0 b1' b0' : Bool, asym2Val b1 b0 = asym2Val b1' b0' → b1 = b1' ∧ b0 = b0') ∧
    (∀ v : Int, (v = -2 ∨ v = -1 ∨ v = 0 ∨ v = 1) ↔ ∃ b1 b0 : Bool, asym2Val b1 b0 = v) ∧
    (∀ v : Int, (v = -1 ∨ v = 0 ∨ v = 1 ∨ v = 2) ↔ ∃ b1 b0 : Bool, -asym2Val b1 b0 = v) ∧
    (∀ xs : List (Bool × Bool × Int),
      xs.foldl (fun acc (b1, b0, a) => acc + asym2Val b1 b0 * a) 0 =
      xs.foldl (fun acc (_, b0, a) => acc + (if b0 then a else 0)) 0 -
      2 * xs.foldl (fun acc (b1, _, a) => acc + (if b1 then a else 0)) 0) := by
  sorry

/-- Theorem 6 (`I091`/`I098` compressor depth inversion):
    The 5-input parity `sum4to2` of any 4:2 compressor cannot be computed by any single `LOP3`
    gate of any 3 of its 5 inputs (forcing `LOP3` depth `≥ 2`), whereas the 3:2 carry-save adder
    (`lop3 0x96`, `lop3 0xE8`) computes exact arithmetic in 2 `LOP3` gates at depth `1`. -/
theorem compressor_4to2_lop3_depth_inversion :
    (∀ i j k : Fin 5, ∀ imm : UInt8,
      ∃ v : Fin 5 → Bool,
        lop3 imm (v i) (v j) (v k) ≠ sum4to2 (v 0) (v 1) (v 2) (v 3) (v 4)) ∧
    (∀ a b c : Bool,
      (if sum3to2 a b c then (1 : Nat) else 0) + 2 * (if carry3to2 a b c then 1 else 0) =
      (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)) := by
  sorry

end SubbyteE2M1Lop3Challenge
