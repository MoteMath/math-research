/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitSerialLutDag

/-!
# Verified Solutions (`bitserial-lut-dag-bounds`)
-/

namespace BitSerialLutDagChallenge

open BitSerialLutDag

theorem binary_lut_dag_lower_bound_exact :
    (∀ (g : Nat) (dag : LinearDag g), 2 ≤ g → computesAllBinary dag →
      binaryLowerBound g ≤ dag.gates.length) ∧
    (∀ (g : Nat) (dag : LinearDag g), 1 ≤ g → computesAllBinary dag →
      g ≤ 2 ^ dagDepth dag ∧ ceilLog2 g ≤ dagDepth dag) ∧
    (∀ (g : Nat) (dag : LinearDag g) (x : Fin g → Int) (m : Nat),
      evalWireVal dag x m = dotInt (evalWireCoeff dag m) x) ∧
    (binaryLowerBound 2 = 2 ∧ binaryLowerBound 3 = 5 ∧
     binaryLowerBound 4 = 10 ∧ binaryLowerBound 5 = 19) ∧
    (ceilLog2 2 = 1 ∧ ceilLog2 3 = 2 ∧ ceilLog2 4 = 2 ∧ ceilLog2 5 = 3) :=
  BitSerialLutDag.binary_lut_dag_lower_bound_exact

theorem tmac_depth2_optimal_12_vs_14_circuit :
    (balancedTreeG4Dag.Valid ∧ balancedTreeG4Dag.isPureAddSub ∧
     balancedTreeG4Dag.gates.length = 12 ∧ dagDepth balancedTreeG4Dag = 2 ∧
     computesAllBinary balancedTreeG4Dag) ∧
    (naiveTmacG4Dag.Valid ∧ naiveTmacG4Dag.isPureAddSub ∧
     naiveTmacG4Dag.gates.length = 14 ∧ dagDepth naiveTmacG4Dag = 3 ∧
     computesAllBinary naiveTmacG4Dag) ∧
    (balancedTreeG4Dag.gates.length < naiveTmacG4Dag.gates.length ∧
     dagDepth balancedTreeG4Dag < dagDepth naiveTmacG4Dag ∧
     dagDepth balancedTreeG4Dag = ceilLog2 4 ∧
     (((naiveTmacG4Dag.gates.length - balancedTreeG4Dag.gates.length : Nat) : Rat) /
        (naiveTmacG4Dag.gates.length : Rat) = 1 / 7) ∧
     (((dagDepth naiveTmacG4Dag - dagDepth balancedTreeG4Dag : Nat) : Rat) /
        (dagDepth naiveTmacG4Dag : Rat) = 1 / 3)) ∧
    (rdna3MidG4Dag.Valid ∧ rdna3MidG4Dag.isRdna3AddLshl ∧
     rdna3MidG4Dag.gates.length = 11 ∧ dagDepth rdna3MidG4Dag = 3 ∧
     computesAllBinary rdna3MidG4Dag) ∧
    (rdna3MinOpsG4Dag.Valid ∧ rdna3MinOpsG4Dag.isRdna3AddLshl ∧
     rdna3MinOpsG4Dag.gates.length = 10 ∧
     rdna3MinOpsG4Dag.gates.length = binaryLowerBound 4 ∧
     dagDepth rdna3MinOpsG4Dag = 4 ∧
     computesAllBinary rdna3MinOpsG4Dag) ∧
    (∀ (x : Fin 4 → Int) (idx : Fin 8),
      (∃ m < 4 + balancedTreeG4Dag.gates.length,
        evalWireVal balancedTreeG4Dag x m = dotInt (binaryTarget 4 idx) x) ∧
      (∃ m < 4 + rdna3MinOpsG4Dag.gates.length,
        evalWireVal rdna3MinOpsG4Dag x m = dotInt (binaryTarget 4 idx) x)) :=
  BitSerialLutDag.tmac_depth2_optimal_12_vs_14_circuit

theorem ternary_lut_dag_bounds_and_symmetry :
    (∀ g : Nat, 2 * ternaryFoldedSize g + 1 = 3 ^ g) ∧
    (ternaryFoldedSize 2 = 4 ∧ ternaryFoldedSize 3 = 13 ∧
     ternaryFoldedSize 4 = 40 ∧ ternaryFoldedSize 5 = 121) ∧
    (ternaryLowerBound 2 = 2 ∧ ternaryLowerBound 3 = 10 ∧
     ternaryLowerBound 4 = 36 ∧ ternaryLowerBound 5 = 116) ∧
    (∀ (g : Nat) (dag : LinearDag g), computesAllTernary dag →
      ternaryLowerBound g ≤ dag.gates.length) ∧
    (∀ (g : Nat) (dag : LinearDag g), 1 ≤ g → computesAllTernary dag →
      g ≤ 2 ^ dagDepth dag ∧ ceilLog2 g ≤ dagDepth dag) ∧
    (ternaryMinG2Dag.Valid ∧ ternaryMinG2Dag.isPureAddSub ∧
     ternaryMinG2Dag.gates.length = 2 ∧ dagDepth ternaryMinG2Dag = 1 ∧
     computesAllTernary ternaryMinG2Dag) ∧
    (ternaryMinG3Dag.Valid ∧ ternaryMinG3Dag.isPureAddSub ∧
     ternaryMinG3Dag.gates.length = 10 ∧ dagDepth ternaryMinG3Dag = 2 ∧
     computesAllTernary ternaryMinG3Dag) ∧
    (ternaryMinG4Dag.Valid ∧ ternaryMinG4Dag.isPureAddSub ∧
     ternaryMinG4Dag.gates.length = 36 ∧ dagDepth ternaryMinG4Dag = 2 ∧
     computesAllTernary ternaryMinG4Dag) ∧
    (ternarySparse2of4Dag.Valid ∧ ternarySparse2of4Dag.isPureAddSub ∧
     ternarySparse2of4Dag.gates.length = 12 ∧ dagDepth ternarySparse2of4Dag = 1 ∧
     countBoundedTernary 4 2 = 16 ∧ computesBoundedTernary ternarySparse2of4Dag 2) :=
  BitSerialLutDag.ternary_lut_dag_bounds_and_symmetry

theorem popcnt_zero_lut_exact_bitserial_dot_identity :
    (∀ (K b : Nat) (signed : Bool) (wPlane : Fin K → Bool) (aPlanes : Fin b → Fin K → Bool),
      dotInt (fun i => binWeight (wPlane i))
        (fun i => bitsToInt b signed (fun j => aPlanes j i)) =
        popcntBinaryDot signed wPlane aPlanes) ∧
    (∀ (K b : Nat) (signed : Bool) (wPos wNeg : Fin K → Bool) (aPlanes : Fin b → Fin K → Bool),
      dotInt (fun i => ternWeight (wPos i) (wNeg i))
        (fun i => bitsToInt b signed (fun j => aPlanes j i)) =
        popcntTernaryDot signed wPos wNeg aPlanes) ∧
    (∀ (b : Nat) (_hb : 1 ≤ b) (x : Int),
      -((2 ^ (b - 1) : Nat) : Int) ≤ x → x < ((2 ^ (b - 1) : Nat) : Int) →
      bitsToInt b true (twosCompBits b x) = x) ∧
    (∀ (K : Nat) (wPlane : Fin K → Bool) (a : Fin K → Int),
      (∀ i, -128 ≤ a i ∧ a i ≤ 127) →
      dotInt (fun i => binWeight (wPlane i)) a =
        popcntBinaryDot true wPlane (fun j i => twosCompBits 8 (a i) j)) ∧
    (∀ (K : Nat) (wPos wNeg : Fin K → Bool) (a : Fin K → Int),
      (∀ i, -128 ≤ a i ∧ a i ≤ 127) →
      dotInt (fun i => ternWeight (wPos i) (wNeg i)) a =
        popcntTernaryDot true wPos wNeg (fun j i => twosCompBits 8 (a i) j)) :=
  BitSerialLutDag.popcnt_zero_lut_exact_bitserial_dot_identity

theorem lut_vs_popcnt_amortization_crossover_exact :
    (∀ (setupPop setupLut steadyPop steadyLut R : Rat),
      (0 : Rat) < R → steadyLut < steadyPop →
      (amortizedCost setupPop steadyPop R < amortizedCost setupLut steadyLut R ↔
        R < (setupLut - setupPop) / (steadyPop - steadyLut))) ∧
    (∀ (setupPop setupLut steadyPop steadyLut : Rat),
      setupPop < setupLut → steadyLut < steadyPop →
      let RStar := (setupLut - setupPop) / (steadyPop - steadyLut)
      (0 : Rat) < RStar ∧
      amortizedCost setupPop steadyPop RStar = amortizedCost setupLut steadyLut RStar) ∧
    (∀ (M N K P g W b cBuild cLut cTr cPop : Rat),
      (0 : Rat) < M → (0 : Rat) < N → (0 : Rat) < K → (0 : Rat) < P →
      cTr ≤ cBuild / g → (b * cPop) / W < cLut / g →
      popcntGemmCost M N K P W b cTr cPop < lutGemmCost M N K P g cBuild cLut) ∧
    (((8 * 2 : Rat) / 32 = 1 / 2) ∧
     ((3 : Rat) / 4 > (8 * 2 : Rat) / 32) ∧
     (((3 : Rat) / 4) / ((8 * 2 : Rat) / 32) = 3 / 2) ∧
     (((1 : Rat) / 4) / ((1 : Rat) / 6) = 3 / 2)) :=
  BitSerialLutDag.lut_vs_popcnt_amortization_crossover_exact

theorem tmac_int16_overflow_threshold_exact :
    (∀ (K : Nat) (w a : Fin K → Int) (wMax aMax : Int),
      0 ≤ wMax → 0 ≤ aMax →
      (∀ i, -wMax ≤ w i ∧ w i ≤ wMax) →
      (∀ i, -aMax ≤ a i ∧ a i ≤ aMax) →
      (K : Int) * (wMax * aMax) ≤ 32767 →
      fitsInt16 (dotInt w a)) ∧
    (∀ (K : Nat) (w a : Fin K → Int),
      K ≤ 258 → (∀ i, -1 ≤ w i ∧ w i ≤ 1) → (∀ i, -127 ≤ a i ∧ a i ≤ 127) →
      fitsInt16 (dotInt w a)) ∧
    (∀ (K : Nat) (w a : Fin K → Int),
      K ≤ 255 → (∀ i, -1 ≤ w i ∧ w i ≤ 1) → (∀ i, -128 ≤ a i ∧ a i ≤ 128) →
      fitsInt16 (dotInt w a)) ∧
    (dotInt (fun _ : Fin 256 => (-1 : Int)) (fun _ : Fin 256 => (-128 : Int)) = int16Max + 1 ∧
     ¬fitsInt16 (dotInt (fun _ : Fin 256 => (-1 : Int)) (fun _ : Fin 256 => (-128 : Int))) ∧
     wrapInt16 (dotInt (fun _ : Fin 256 => (-1 : Int)) (fun _ : Fin 256 => (-128 : Int))) = int16Min) ∧
    (dotInt (fun _ : Fin 128 => (-2 : Int)) (fun _ : Fin 128 => (-128 : Int)) = int16Max + 1 ∧
     wrapInt16 (dotInt (fun _ : Fin 128 => (-2 : Int)) (fun _ : Fin 128 => (-128 : Int))) = int16Min) ∧
    (dotInt (fun _ : Fin 64 => (-4 : Int)) (fun _ : Fin 64 => (-128 : Int)) = int16Max + 1 ∧
     wrapInt16 (dotInt (fun _ : Fin 64 => (-4 : Int)) (fun _ : Fin 64 => (-128 : Int))) = int16Min) :=
  BitSerialLutDag.tmac_int16_overflow_threshold_exact

end BitSerialLutDagChallenge
