# Audit record

This file records the checks run on the exact sources in `bitwise-carry-algebra/`.

Toolchain: Lean `leanprover/lean4:v4.34.1`, `Init` only (zero Mathlib).

## How to reproduce

```sh
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

## Recorded results

- `lake build`: completed successfully (7 jobs); zero errors and zero warnings across `BitwiseCarryAlgebra.*` and `Solution`.
- `lake build Challenge`: completed with 8 expected `declaration uses 'sorry'` warnings in `Challenge.lean` only.
- Custom axioms (`axiom ...`) outside comments: **0**.
- Occurrences of `sorry` outside `Challenge.lean`: **0**.
- Axiom audit: every headline theorem uses only standard Lean axioms within `[propext, Classical.choice, Quot.sound]`.

### `#print axioms` output (`scripts/PrintAxioms.lean`), verbatim

```text
'BitwiseCarryChallenge.carryWord_cocycle' depends on axioms: [propext, Quot.sound]
'BitwiseCarryChallenge.carryPop_cocycle' depends on axioms: [propext, Quot.sound]
'BitwiseCarryChallenge.gray_add_xor_eq_gray_carryWord' depends on axioms: [propext, Quot.sound]
'BitwiseCarryChallenge.popcnt_gray_carryWord' depends on axioms: [propext, Classical.choice, Quot.sound]
'BitwiseCarryChallenge.borrowWord_eq_carryWord' depends on axioms: [propext, Quot.sound]
'BitwiseCarryChallenge.sumSquare_carryPop' depends on axioms: [propext, Quot.sound]
'BitwiseCarryChallenge.sumSquare_carryBlocks' depends on axioms: [propext, Quot.sound]
'BitwiseCarryChallenge.count_zero_and_one_carryBlock' depends on axioms: [propext, Classical.choice, Quot.sound]
```
