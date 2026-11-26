# Audit record

This file records the checks run on the exact sources in `carry-blocks-determinants/`.

Toolchain: Lean `leanprover/lean4:v4.34.1`, Mathlib `v4.34.1`.

## How to reproduce

```sh
lake exe cache get
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

## Recorded results

- `lake build`: completed successfully (3099 jobs); zero errors and zero warnings across `CarryBlocksDeterminants.*` and `Solution`.
- `lake build Challenge`: completed with 10 expected `declaration uses 'sorry'` warnings in `Challenge.lean` only.
- Custom axioms (`axiom ...`) outside comments: **0**.
- Occurrences of `sorry` outside `Challenge.lean`: **0**.
- Axiom audit: every headline theorem uses only standard Lean axioms `[propext, Classical.choice, Quot.sound]`.

### `#print axioms` output (`scripts/PrintAxioms.lean`), verbatim

```text
'CarryBlocksChallenge.det_mixedCarryBlocks_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryBlocksChallenge.det_mixedCarryBlocks_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryBlocksChallenge.det_binaryCarryBlocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryBlocksChallenge.det_grayCarryTransitions' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryBlocksChallenge.det_plateauHankel_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryBlocksChallenge.det_plateauHankel_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryBlocksChallenge.det_mixedDigitLen_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryBlocksChallenge.det_mixedDigitLen_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryBlocksChallenge.det_bitlen_xor_add_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryBlocksChallenge.det_bitlen_xor' depends on axioms: [propext, Classical.choice, Quot.sound]
```
