# Audit record

This file records the checks run on the exact sources in `combinatorial-inequalities/`.

Toolchain: Lean `leanprover/lean4:v4.34.1`, `Std` only (no Mathlib dependency).

## How to reproduce

```sh
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

## Recorded results

- `lake build`: completed successfully (7 jobs); zero errors and zero warnings across `CombInequalities.*` and `Solution`.
- `lake build Challenge`: completed with 4 expected `declaration uses 'sorry'` warnings in `Challenge.lean` only.
- Custom axioms (`axiom ...`) outside comments: **0**.
- Occurrences of `sorry` outside `Challenge.lean`: **0**.
- Every headline theorem depends only on a subset of `{propext, Classical.choice, Quot.sound}`.

### `#print axioms` output (`scripts/PrintAxioms.lean`), verbatim

```text
'CombInequalitiesChallenge.avoids321_three_stack2Inv_le_pat231' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CombInequalitiesChallenge.stackDes_le_peaksCnt' depends on axioms: [propext, Quot.sound]
'CombInequalitiesChallenge.avoids231_two_inv_le_disp2_add_des' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CombInequalitiesChallenge.three_diffset_le_two_sum2Diff1_add_one' depends on axioms: [propext, Quot.sound]
```
