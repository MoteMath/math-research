# Audit record

This file records the checks run on the exact sources in `weak-bruhat-commutators/`.

Toolchain: Lean `leanprover/lean4:v4.34.1`, `Init` only (zero Mathlib).

## How to reproduce

```sh
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

## Recorded results

- `lake build`: completed successfully (10 jobs); zero errors and zero warnings across `WeakBruhatCommutators.*` and `Solution`.
- `lake build Challenge`: completed with 8 expected `declaration uses 'sorry'` warnings in `Challenge.lean` only.
- Custom axioms (`axiom ...`) outside comments: **0**.
- Occurrences of `sorry` outside `Challenge.lean`: **0**.
- Axiom audit: every headline theorem uses only standard Lean 4 axioms (`[propext, Classical.choice, Quot.sound]`).

### `#print axioms` output (`scripts/PrintAxioms.lean`), verbatim

```text
'WeakBruhatCommutatorsChallenge.desBot_bubblePass_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeakBruhatCommutatorsChallenge.bubbleOrder_bubblePass_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeakBruhatCommutatorsChallenge.iterBubble_west_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeakBruhatCommutatorsChallenge.iterBubble_pop_commutator' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeakBruhatCommutatorsChallenge.invCnt_iterBubble_west_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeakBruhatCommutatorsChallenge.desCnt_iterBubble_west_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeakBruhatCommutatorsChallenge.invCnt_iterBubble_pop_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeakBruhatCommutatorsChallenge.desCnt_iterBubble_pop_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```
