/-
Copyright (c) 2026 MoteMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BitSerialLutDag.Defs

/-!
# Trusted Challenge Statements (`bitserial-lut-dag-bounds`)

Universal and exact pure-`Init` (zero Mathlib) Lean 4 statements for:
1. Universal 2-input linear DAG lower bound `2^(g-1) + g - 2` ops and `ceilLog2 g` depth
   for sign-folded binary LUT precomputation (`2, 5, 10, 19` ops for `g = 2, 3, 4, 5`).
2. Exact soundness, completeness, and Pareto dominance of the GPU-discovered `g = 4`
   balanced `(12 ops, depth 2)` binary LUT circuit over naive T-MAC `(14 ops, depth 3)`
   alongside the RDNA 3 `V_ADD_LSHL` `(11 ops, depth 3)` and `(10 ops, depth 4)` circuits.
3. Exact symmetry-halved ternary LUT size `(3^g - 1)/2` (`4, 13, 40, 121`), universal lower
   bound `(3^g - 1)/2 - g` ops and `ceilLog2 g` depth, minimal zero-waste ternary DAGs
   for `g = 2, 3, 4`, and structured `(≤2, 4)` ternary sparsity compression (`12 ops, depth 1`).
4. Universal exact bit-serial `POPCNT` dot-product identity for binary `{-1, +1}` and
   ternary `{-1, 0, +1}` weights against arbitrary `b`-bit signed or unsigned activations.
5. Exact LUT-vs-`POPCNT` amortization crossover law and RDNA 3 no-crossover dominance theorem.
6. Exact `int16` accumulation overflow thresholds (`K_max = 258` symmetric vs `K_max = 255`
   full `int8` two's-complement wrap-by-1 trap at `K = 256`).
-/

namespace BitSerialLutDagChallenge

open BitSerialLutDag

/-- Theorem 1 (`binary_lut_dag_lower_bound_exact`):
    Universal gate-count lower bound `2^(g-1) + g - 2` and depth lower bound `ceilLog2 g`
    for any 2-input linear DAG computing all sign-canonical binary LUT entries, plus exact
    specializations for `g = 2, 3, 4, 5`. -/
theorem binary_lut_dag_lower_bound_exact :
    (∀ (g : Nat) (dag : LinearDag g), 2 ≤ g → computesAllBinary dag →
      binaryLowerBound g ≤ dag.gates.length) ∧
    (∀ (g : Nat) (dag : LinearDag g), 1 ≤ g → computesAllBinary dag →
      g ≤ 2 ^ dagDepth dag ∧ ceilLog2 g ≤ dagDepth dag) ∧
    (∀ (g : Nat) (dag : LinearDag g) (x : Fin g → Int) (m : Nat),
      evalWireVal dag x m = dotInt (evalWireCoeff dag m) x) ∧
    (binaryLowerBound 2 = 2 ∧ binaryLowerBound 3 = 5 ∧
     binaryLowerBound 4 = 10 ∧ binaryLowerBound 5 = 19) ∧
    (ceilLog2 2 = 1 ∧ ceilLog2 3 = 2 ∧ ceilLog2 4 = 2 ∧ ceilLog2 5 = 3) := by
  sorry

/-- Theorem 2 (`tmac_depth2_optimal_12_vs_14_circuit`):
    Exact soundness, completeness, and Pareto dominance of the GPU-discovered `g = 4`
    circuits: balanced `(12 ops, depth 2)` strictly beats naive T-MAC `(14 ops, depth 3)`
    in both op count (`-1/7 = -14.3%`) and depth (`-1/3 = -33.3%`) while matching `ceilLog2 4 = 2`,
    and the RDNA 3 `V_ADD_LSHL` circuits achieve `(11 ops, depth 3)` and lower-bound-tight
    `(10 ops, depth 4)` (= `binaryLowerBound 4`). -/
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
        evalWireVal rdna3MinOpsG4Dag x m = dotInt (binaryTarget 4 idx) x)) := by
  sorry

/-- Theorem 3 (`ternary_lut_dag_bounds_and_symmetry`):
    Proves exact symmetry-halved ternary LUT size `2 * ternaryFoldedSize g + 1 = 3 ^ g`
    (`4, 13, 40, 121` for `g = 2, 3, 4, 5`), universal lower bounds `(3^g - 1)/2 - g` ops
    and `ceilLog2 g` depth, exact soundness & zero-waste optimality of the minimal ternary
    DAGs for `g = 2, 3, 4`, and the structured `(≤2, 4)` ternary sparsity DAG (`12 ops, depth 1`,
    `16` entries vs `40`). -/
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
     countBoundedTernary 4 2 = 16 ∧ computesBoundedTernary ternarySparse2of4Dag 2) := by
  sorry

/-- Theorem 4 (`popcnt_zero_lut_exact_bitserial_dot_identity`):
    Universal bit-exact bit-serial `POPCNT` dot-product identity for binary `{-1, +1}`
    and ternary `{-1, 0, +1}` weights against arbitrary `b`-bit signed/unsigned activations,
    plus universal `b`-bit two's-complement roundtrip and exact `int8` specialization. -/
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
        popcntTernaryDot true wPos wNeg (fun j i => twosCompBits 8 (a i) j)) := by
  sorry

/-- Theorem 5 (`lut_vs_popcnt_amortization_crossover_exact`):
    Exact symbolic amortization crossover `R* = (setupLut - setupPop) / (steadyPop - steadyLut)`
    explaining why zero-LUT `POPCNT` wins on small-batch LLM decode (`R < R*`), plus the
    exact RDNA 3 (`gfx1100`) no-crossover dominance theorem (`POPCNT` wins for all `M, N, K > 0`)
    and exact `gfx1100` cost ratios (`1/2 < 3/4` steady-state, `3/2×` `g=6` vs `g=4` lookups). -/
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
     (((1 : Rat) / 4) / ((1 : Rat) / 6) = 3 / 2)) := by
  sorry

/-- Theorem 6 (`tmac_int16_overflow_threshold_exact`):
    Proves universal `int16` accumulation safety, the exact symmetric `int8` ceiling
    `K_max = 258` (making `K_tile = 256` zero-overflow), and the exact full `int8`
    two's-complement wrap-by-1 trap (`+32768 ↦ -32768`) at `K = 256` (`wMax = 1`),
    `K = 128` (direct INT2 `wMax = 2`), and `K = 64` (direct INT3 `wMax = 4`). -/
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
     wrapInt16 (dotInt (fun _ : Fin 64 => (-4 : Int)) (fun _ : Fin 64 => (-128 : Int))) = int16Min) := by
  sorry

end BitSerialLutDagChallenge
