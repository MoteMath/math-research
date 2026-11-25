# Audit record

This file records the checks run on the exact sources in `bit-circuit-synthesis/`.

Toolchain: Lean `leanprover/lean4:v4.34.1`, `Init` only (no Mathlib, no built-in `Nat`/`Int`/`Bool` arithmetic).

## How to reproduce

```sh
lake build
lake build Challenge
lake env lean scripts/PrintAxioms.lean
```

## Recorded results

- `lake build`: completed successfully (26 jobs); zero errors and zero warnings across `BitCircuitSynthesis.*` and `Solution`.
- `lake build Challenge`: completed with 8 expected `declaration uses 'sorry'` warnings in `Challenge.lean` only.
- Custom axioms (`axiom ...`) outside comments: **0**.
- Occurrences of `sorry` outside `Challenge.lean`: **0**.
- Axiom audit: every headline theorem uses at most `[propext]` (no `Classical.choice`, no `Quot.sound`); `bcarried_vs_carryless_deg_jump_witness` uses **zero axioms**.

### `#print axioms` output (`scripts/PrintAxioms.lean`), verbatim

```text
'BitCircuitChallenge.bpos_clmul_deg_additive' depends on axioms: [propext]
'BitCircuitChallenge.bf2x_integral_domain' depends on axioms: [propext]
'BitCircuitChallenge.bcarried_vs_carryless_deg_jump_witness' does not depend on any axioms
'BitCircuitChallenge.bartin_schreier_add_hom' depends on axioms: [propext]
'BitCircuitChallenge.bartin_schreier_shift_one_inv' depends on axioms: [propext]
'BitCircuitChallenge.bfrob2_xor_hom' depends on axioms: [propext]
'BitCircuitChallenge.bfrob_trace_artin_schreier_telescope' depends on axioms: [propext]
'BitCircuitChallenge.bhilbert90_additive_trace_zero_mod' depends on axioms: [propext]
```
