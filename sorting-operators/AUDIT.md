# Audit record

This file records the checks run on the exact sources in `sorting-operators/`.

Toolchain: Lean `leanprover/lean4:v4.34.1`, `Init` only (zero Mathlib).

## How to reproduce

```sh
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

## Recorded results

- `lake build`: completed successfully (7 jobs); zero errors and zero warnings across `SortingOperators.*` and `Solution`.
- `lake build Challenge`: completed with 5 expected `declaration uses 'sorry'` warnings in `Challenge.lean` only.
- Custom axioms (`axiom ...`) outside comments: **0**.
- Occurrences of `sorry` outside `Challenge.lean`: **0**.
- Axiom audit: every headline theorem uses only `[propext, Quot.sound]` (no `Classical.choice`).

### `#print axioms` output (`scripts/PrintAxioms.lean`), verbatim

```text
'SortingOperatorsChallenge.inv_westSort_le_bubble' depends on axioms: [propext, Quot.sound]
'SortingOperatorsChallenge.des_westSort_le_bubble' depends on axioms: [propext, Quot.sound]
'SortingOperatorsChallenge.westSort_eq_bubble_of_avoids321' depends on axioms: [propext, Quot.sound]
'SortingOperatorsChallenge.exists_not_avoids321_westSort_eq_bubble' depends on axioms: [propext, Quot.sound]
'SortingOperatorsChallenge.inv_bubble_le_pat321_add_pat231' depends on axioms: [propext, Quot.sound]
```
