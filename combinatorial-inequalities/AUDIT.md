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

- `lake build`: completed successfully (8 jobs); zero errors and zero warnings across `CombInequalities.*` and `Solution`.
- `lake build Challenge`: completed with 12 expected `declaration uses 'sorry'` warnings in `Challenge.lean` only.
- Custom axioms (`axiom ...`) outside comments: **0**.
- Occurrences of `sorry` outside `Challenge.lean`: **0**.
- Every headline theorem depends only on a subset of `{propext, Classical.choice, Quot.sound}`.

### `#print axioms` output (`scripts/PrintAxioms.lean`), verbatim

```text
'CombInequalitiesChallenge.stackInv_le_popInv' depends on axioms: [propext, Quot.sound]
'CombInequalitiesChallenge.avoids321_three_stack2Inv_le_pat231' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CombInequalitiesChallenge.stackDes_le_peaksCnt' depends on axioms: [propext, Quot.sound]
'CombInequalitiesChallenge.stackInv_le_pat231' depends on axioms: [propext, Quot.sound]
'CombInequalitiesChallenge.avoids231_two_inv_le_disp2_add_des' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CombInequalitiesChallenge.sidon_sym_defect_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'CombInequalitiesChallenge.two_card_add_symDefect_le_diffset_add_one' depends on axioms: [propext, Quot.sound]
'CombInequalitiesChallenge.three_diffset_le_two_sum2Diff1_add_one' depends on axioms: [propext, Quot.sound]
'CombInequalitiesChallenge.connected_diam_le_indP4_add_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'CombInequalitiesChallenge.albertson_le_orderedIndP3' depends on axioms: [propext, Quot.sound]
'CombInequalitiesChallenge.disproof_avoids231_inv_disp_lds' depends on axioms: [propext, Quot.sound]
'CombInequalitiesChallenge.disproof_bipartite_dom_indNu_diam' depends on axioms: [propext, Quot.sound]
```
