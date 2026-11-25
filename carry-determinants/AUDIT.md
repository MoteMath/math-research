# Audit record

This file records the checks run on the exact sources in `carry-determinants/`.

Toolchain: Lean `leanprover/lean4:v4.34.1`; Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612` (`v4.34.1`, pinned in `lake-manifest.json`).

## How to reproduce

```sh
lake exe cache get
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

## Recorded results

- `lake build`: completed successfully (2,249 jobs including the Mathlib dependency closure); zero errors and zero warnings across `CarryDeterminants.*` and `Solution`.
- `lake build Challenge`: completed with 11 expected `declaration uses 'sorry'` warnings in `Challenge.lean` only.
- Custom axioms (`axiom ...`) outside comments: **0**.
- Occurrences of `sorry` outside `Challenge.lean`: **0**.
- Every headline theorem depends only on Lean's three standard axioms `[propext, Classical.choice, Quot.sound]`.

### `#print axioms` output (`scripts/PrintAxioms.lean`), verbatim

```text
'CarryDeterminantsChallenge.carryMatrix_det_eq_zero_of_non_extremal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryDeterminantsChallenge.existsUnique_placeValue_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryDeterminantsChallenge.mixedCarryPolyMatrix_det_ne_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryDeterminantsChallenge.baseCarryPolyMatrix_det_ne_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryDeterminantsChallenge.binaryCarryPolyMatrix_det_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CarryDeterminantsChallenge.det_mixedHankelMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryDeterminantsChallenge.det_carryMatrix_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryDeterminantsChallenge.det_weightedLinearCarryMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryDeterminantsChallenge.det_kummer_padicValNat_choose' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryDeterminantsChallenge.det_binary_carry_word' depends on axioms: [propext, Classical.choice, Quot.sound]
'CarryDeterminantsChallenge.det_thueMorse_pow_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```
